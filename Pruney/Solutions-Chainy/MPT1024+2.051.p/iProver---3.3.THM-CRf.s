%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:57 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 341 expanded)
%              Number of clauses        :   58 ( 115 expanded)
%              Number of leaves         :   15 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  400 (1614 expanded)
%              Number of equality atoms :  122 ( 366 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
              ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK1(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2)
                  & r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
                    & r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).

fof(f43,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ r2_hidden(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f20,f33,f32])).

fof(f53,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f56,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_529,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_530,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_1414,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_515,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_1415,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1431,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2827,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X2) = iProver_top
    | r1_tarski(k1_relat_1(sK7),X2) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1415,c_1431])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1422,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1429,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1830,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_1429])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_175,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_220,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_176])).

cnf(c_1656,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_2035,plain,
    ( ~ r1_tarski(sK7,k2_zfmisc_1(sK4,sK5))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1656])).

cnf(c_2037,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2035])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2676,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2677,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2676])).

cnf(c_4760,plain,
    ( r1_tarski(k1_relat_1(sK7),X2) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2827,c_1830,c_2037,c_2677])).

cnf(c_4761,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X2) = iProver_top
    | r1_tarski(k1_relat_1(sK7),X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4760])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1425,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2566,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1422,c_1425])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1423,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2949,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2566,c_1423])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_544,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_545,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_1413,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_3000,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_1413])).

cnf(c_3073,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3000,c_1830,c_2037,c_2677])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1424,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3077,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3073,c_1424])).

cnf(c_4776,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4761,c_3077])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1426,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2699,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1422,c_1426])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1427,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2946,plain,
    ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2699,c_1427])).

cnf(c_23,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3206,plain,
    ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2946,c_23])).

cnf(c_3211,plain,
    ( r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_1429])).

cnf(c_4857,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4776,c_2949,c_3211])).

cnf(c_4862,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_4857])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4862,c_2949,c_2677,c_2037,c_1830])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:59:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.03/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/0.98  
% 3.03/0.98  ------  iProver source info
% 3.03/0.98  
% 3.03/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.03/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/0.98  git: non_committed_changes: false
% 3.03/0.98  git: last_make_outside_of_git: false
% 3.03/0.98  
% 3.03/0.98  ------ 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options
% 3.03/0.98  
% 3.03/0.98  --out_options                           all
% 3.03/0.98  --tptp_safe_out                         true
% 3.03/0.98  --problem_path                          ""
% 3.03/0.98  --include_path                          ""
% 3.03/0.98  --clausifier                            res/vclausify_rel
% 3.03/0.98  --clausifier_options                    --mode clausify
% 3.03/0.98  --stdin                                 false
% 3.03/0.98  --stats_out                             all
% 3.03/0.98  
% 3.03/0.98  ------ General Options
% 3.03/0.98  
% 3.03/0.98  --fof                                   false
% 3.03/0.98  --time_out_real                         305.
% 3.03/0.98  --time_out_virtual                      -1.
% 3.03/0.98  --symbol_type_check                     false
% 3.03/0.98  --clausify_out                          false
% 3.03/0.98  --sig_cnt_out                           false
% 3.03/0.98  --trig_cnt_out                          false
% 3.03/0.98  --trig_cnt_out_tolerance                1.
% 3.03/0.98  --trig_cnt_out_sk_spl                   false
% 3.03/0.98  --abstr_cl_out                          false
% 3.03/0.98  
% 3.03/0.98  ------ Global Options
% 3.03/0.98  
% 3.03/0.98  --schedule                              default
% 3.03/0.98  --add_important_lit                     false
% 3.03/0.98  --prop_solver_per_cl                    1000
% 3.03/0.98  --min_unsat_core                        false
% 3.03/0.98  --soft_assumptions                      false
% 3.03/0.98  --soft_lemma_size                       3
% 3.03/0.98  --prop_impl_unit_size                   0
% 3.03/0.98  --prop_impl_unit                        []
% 3.03/0.98  --share_sel_clauses                     true
% 3.03/0.98  --reset_solvers                         false
% 3.03/0.98  --bc_imp_inh                            [conj_cone]
% 3.03/0.98  --conj_cone_tolerance                   3.
% 3.03/0.98  --extra_neg_conj                        none
% 3.03/0.98  --large_theory_mode                     true
% 3.03/0.98  --prolific_symb_bound                   200
% 3.03/0.98  --lt_threshold                          2000
% 3.03/0.98  --clause_weak_htbl                      true
% 3.03/0.98  --gc_record_bc_elim                     false
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing Options
% 3.03/0.98  
% 3.03/0.98  --preprocessing_flag                    true
% 3.03/0.98  --time_out_prep_mult                    0.1
% 3.03/0.98  --splitting_mode                        input
% 3.03/0.98  --splitting_grd                         true
% 3.03/0.98  --splitting_cvd                         false
% 3.03/0.98  --splitting_cvd_svl                     false
% 3.03/0.98  --splitting_nvd                         32
% 3.03/0.98  --sub_typing                            true
% 3.03/0.98  --prep_gs_sim                           true
% 3.03/0.98  --prep_unflatten                        true
% 3.03/0.98  --prep_res_sim                          true
% 3.03/0.98  --prep_upred                            true
% 3.03/0.98  --prep_sem_filter                       exhaustive
% 3.03/0.98  --prep_sem_filter_out                   false
% 3.03/0.98  --pred_elim                             true
% 3.03/0.98  --res_sim_input                         true
% 3.03/0.98  --eq_ax_congr_red                       true
% 3.03/0.98  --pure_diseq_elim                       true
% 3.03/0.98  --brand_transform                       false
% 3.03/0.98  --non_eq_to_eq                          false
% 3.03/0.98  --prep_def_merge                        true
% 3.03/0.98  --prep_def_merge_prop_impl              false
% 3.03/0.98  --prep_def_merge_mbd                    true
% 3.03/0.98  --prep_def_merge_tr_red                 false
% 3.03/0.98  --prep_def_merge_tr_cl                  false
% 3.03/0.98  --smt_preprocessing                     true
% 3.03/0.98  --smt_ac_axioms                         fast
% 3.03/0.98  --preprocessed_out                      false
% 3.03/0.98  --preprocessed_stats                    false
% 3.03/0.98  
% 3.03/0.98  ------ Abstraction refinement Options
% 3.03/0.98  
% 3.03/0.98  --abstr_ref                             []
% 3.03/0.98  --abstr_ref_prep                        false
% 3.03/0.98  --abstr_ref_until_sat                   false
% 3.03/0.98  --abstr_ref_sig_restrict                funpre
% 3.03/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.98  --abstr_ref_under                       []
% 3.03/0.98  
% 3.03/0.98  ------ SAT Options
% 3.03/0.98  
% 3.03/0.98  --sat_mode                              false
% 3.03/0.98  --sat_fm_restart_options                ""
% 3.03/0.98  --sat_gr_def                            false
% 3.03/0.98  --sat_epr_types                         true
% 3.03/0.98  --sat_non_cyclic_types                  false
% 3.03/0.98  --sat_finite_models                     false
% 3.03/0.98  --sat_fm_lemmas                         false
% 3.03/0.98  --sat_fm_prep                           false
% 3.03/0.98  --sat_fm_uc_incr                        true
% 3.03/0.98  --sat_out_model                         small
% 3.03/0.98  --sat_out_clauses                       false
% 3.03/0.98  
% 3.03/0.98  ------ QBF Options
% 3.03/0.98  
% 3.03/0.98  --qbf_mode                              false
% 3.03/0.98  --qbf_elim_univ                         false
% 3.03/0.98  --qbf_dom_inst                          none
% 3.03/0.98  --qbf_dom_pre_inst                      false
% 3.03/0.98  --qbf_sk_in                             false
% 3.03/0.98  --qbf_pred_elim                         true
% 3.03/0.98  --qbf_split                             512
% 3.03/0.98  
% 3.03/0.98  ------ BMC1 Options
% 3.03/0.98  
% 3.03/0.98  --bmc1_incremental                      false
% 3.03/0.98  --bmc1_axioms                           reachable_all
% 3.03/0.98  --bmc1_min_bound                        0
% 3.03/0.98  --bmc1_max_bound                        -1
% 3.03/0.98  --bmc1_max_bound_default                -1
% 3.03/0.98  --bmc1_symbol_reachability              true
% 3.03/0.98  --bmc1_property_lemmas                  false
% 3.03/0.98  --bmc1_k_induction                      false
% 3.03/0.98  --bmc1_non_equiv_states                 false
% 3.03/0.98  --bmc1_deadlock                         false
% 3.03/0.98  --bmc1_ucm                              false
% 3.03/0.98  --bmc1_add_unsat_core                   none
% 3.03/0.98  --bmc1_unsat_core_children              false
% 3.03/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.98  --bmc1_out_stat                         full
% 3.03/0.98  --bmc1_ground_init                      false
% 3.03/0.98  --bmc1_pre_inst_next_state              false
% 3.03/0.98  --bmc1_pre_inst_state                   false
% 3.03/0.98  --bmc1_pre_inst_reach_state             false
% 3.03/0.98  --bmc1_out_unsat_core                   false
% 3.03/0.98  --bmc1_aig_witness_out                  false
% 3.03/0.98  --bmc1_verbose                          false
% 3.03/0.98  --bmc1_dump_clauses_tptp                false
% 3.03/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.98  --bmc1_dump_file                        -
% 3.03/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.98  --bmc1_ucm_extend_mode                  1
% 3.03/0.98  --bmc1_ucm_init_mode                    2
% 3.03/0.98  --bmc1_ucm_cone_mode                    none
% 3.03/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.98  --bmc1_ucm_relax_model                  4
% 3.03/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.98  --bmc1_ucm_layered_model                none
% 3.03/0.98  --bmc1_ucm_max_lemma_size               10
% 3.03/0.98  
% 3.03/0.98  ------ AIG Options
% 3.03/0.98  
% 3.03/0.98  --aig_mode                              false
% 3.03/0.98  
% 3.03/0.98  ------ Instantiation Options
% 3.03/0.98  
% 3.03/0.98  --instantiation_flag                    true
% 3.03/0.98  --inst_sos_flag                         false
% 3.03/0.98  --inst_sos_phase                        true
% 3.03/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel_side                     num_symb
% 3.03/0.98  --inst_solver_per_active                1400
% 3.03/0.98  --inst_solver_calls_frac                1.
% 3.03/0.98  --inst_passive_queue_type               priority_queues
% 3.03/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.98  --inst_passive_queues_freq              [25;2]
% 3.03/0.98  --inst_dismatching                      true
% 3.03/0.98  --inst_eager_unprocessed_to_passive     true
% 3.03/0.98  --inst_prop_sim_given                   true
% 3.03/0.98  --inst_prop_sim_new                     false
% 3.03/0.98  --inst_subs_new                         false
% 3.03/0.98  --inst_eq_res_simp                      false
% 3.03/0.98  --inst_subs_given                       false
% 3.03/0.98  --inst_orphan_elimination               true
% 3.03/0.98  --inst_learning_loop_flag               true
% 3.03/0.98  --inst_learning_start                   3000
% 3.03/0.98  --inst_learning_factor                  2
% 3.03/0.98  --inst_start_prop_sim_after_learn       3
% 3.03/0.98  --inst_sel_renew                        solver
% 3.03/0.98  --inst_lit_activity_flag                true
% 3.03/0.98  --inst_restr_to_given                   false
% 3.03/0.98  --inst_activity_threshold               500
% 3.03/0.98  --inst_out_proof                        true
% 3.03/0.98  
% 3.03/0.98  ------ Resolution Options
% 3.03/0.98  
% 3.03/0.98  --resolution_flag                       true
% 3.03/0.98  --res_lit_sel                           adaptive
% 3.03/0.98  --res_lit_sel_side                      none
% 3.03/0.98  --res_ordering                          kbo
% 3.03/0.98  --res_to_prop_solver                    active
% 3.03/0.98  --res_prop_simpl_new                    false
% 3.03/0.98  --res_prop_simpl_given                  true
% 3.03/0.98  --res_passive_queue_type                priority_queues
% 3.03/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.98  --res_passive_queues_freq               [15;5]
% 3.03/0.98  --res_forward_subs                      full
% 3.03/0.98  --res_backward_subs                     full
% 3.03/0.98  --res_forward_subs_resolution           true
% 3.03/0.98  --res_backward_subs_resolution          true
% 3.03/0.98  --res_orphan_elimination                true
% 3.03/0.98  --res_time_limit                        2.
% 3.03/0.98  --res_out_proof                         true
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Options
% 3.03/0.98  
% 3.03/0.98  --superposition_flag                    true
% 3.03/0.98  --sup_passive_queue_type                priority_queues
% 3.03/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.98  --demod_completeness_check              fast
% 3.03/0.98  --demod_use_ground                      true
% 3.03/0.98  --sup_to_prop_solver                    passive
% 3.03/0.98  --sup_prop_simpl_new                    true
% 3.03/0.98  --sup_prop_simpl_given                  true
% 3.03/0.98  --sup_fun_splitting                     false
% 3.03/0.98  --sup_smt_interval                      50000
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Simplification Setup
% 3.03/0.98  
% 3.03/0.98  --sup_indices_passive                   []
% 3.03/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_full_bw                           [BwDemod]
% 3.03/0.98  --sup_immed_triv                        [TrivRules]
% 3.03/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_immed_bw_main                     []
% 3.03/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  
% 3.03/0.98  ------ Combination Options
% 3.03/0.98  
% 3.03/0.98  --comb_res_mult                         3
% 3.03/0.98  --comb_sup_mult                         2
% 3.03/0.98  --comb_inst_mult                        10
% 3.03/0.98  
% 3.03/0.98  ------ Debug Options
% 3.03/0.98  
% 3.03/0.98  --dbg_backtrace                         false
% 3.03/0.98  --dbg_dump_prop_clauses                 false
% 3.03/0.98  --dbg_dump_prop_clauses_file            -
% 3.03/0.98  --dbg_out_stat                          false
% 3.03/0.98  ------ Parsing...
% 3.03/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/0.98  ------ Proving...
% 3.03/0.98  ------ Problem Properties 
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  clauses                                 21
% 3.03/0.98  conjectures                             3
% 3.03/0.98  EPR                                     2
% 3.03/0.98  Horn                                    17
% 3.03/0.98  unary                                   3
% 3.03/0.98  binary                                  7
% 3.03/0.98  lits                                    57
% 3.03/0.98  lits eq                                 10
% 3.03/0.98  fd_pure                                 0
% 3.03/0.98  fd_pseudo                               0
% 3.03/0.98  fd_cond                                 0
% 3.03/0.98  fd_pseudo_cond                          4
% 3.03/0.98  AC symbols                              0
% 3.03/0.98  
% 3.03/0.98  ------ Schedule dynamic 5 is on 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  ------ 
% 3.03/0.98  Current options:
% 3.03/0.98  ------ 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options
% 3.03/0.98  
% 3.03/0.98  --out_options                           all
% 3.03/0.98  --tptp_safe_out                         true
% 3.03/0.98  --problem_path                          ""
% 3.03/0.98  --include_path                          ""
% 3.03/0.98  --clausifier                            res/vclausify_rel
% 3.03/0.98  --clausifier_options                    --mode clausify
% 3.03/0.98  --stdin                                 false
% 3.03/0.98  --stats_out                             all
% 3.03/0.98  
% 3.03/0.98  ------ General Options
% 3.03/0.98  
% 3.03/0.98  --fof                                   false
% 3.03/0.98  --time_out_real                         305.
% 3.03/0.98  --time_out_virtual                      -1.
% 3.03/0.98  --symbol_type_check                     false
% 3.03/0.98  --clausify_out                          false
% 3.03/0.98  --sig_cnt_out                           false
% 3.03/0.98  --trig_cnt_out                          false
% 3.03/0.98  --trig_cnt_out_tolerance                1.
% 3.03/0.98  --trig_cnt_out_sk_spl                   false
% 3.03/0.98  --abstr_cl_out                          false
% 3.03/0.98  
% 3.03/0.98  ------ Global Options
% 3.03/0.98  
% 3.03/0.98  --schedule                              default
% 3.03/0.98  --add_important_lit                     false
% 3.03/0.98  --prop_solver_per_cl                    1000
% 3.03/0.98  --min_unsat_core                        false
% 3.03/0.98  --soft_assumptions                      false
% 3.03/0.98  --soft_lemma_size                       3
% 3.03/0.98  --prop_impl_unit_size                   0
% 3.03/0.98  --prop_impl_unit                        []
% 3.03/0.98  --share_sel_clauses                     true
% 3.03/0.98  --reset_solvers                         false
% 3.03/0.98  --bc_imp_inh                            [conj_cone]
% 3.03/0.98  --conj_cone_tolerance                   3.
% 3.03/0.98  --extra_neg_conj                        none
% 3.03/0.98  --large_theory_mode                     true
% 3.03/0.98  --prolific_symb_bound                   200
% 3.03/0.98  --lt_threshold                          2000
% 3.03/0.98  --clause_weak_htbl                      true
% 3.03/0.98  --gc_record_bc_elim                     false
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing Options
% 3.03/0.98  
% 3.03/0.98  --preprocessing_flag                    true
% 3.03/0.98  --time_out_prep_mult                    0.1
% 3.03/0.98  --splitting_mode                        input
% 3.03/0.98  --splitting_grd                         true
% 3.03/0.98  --splitting_cvd                         false
% 3.03/0.98  --splitting_cvd_svl                     false
% 3.03/0.98  --splitting_nvd                         32
% 3.03/0.98  --sub_typing                            true
% 3.03/0.98  --prep_gs_sim                           true
% 3.03/0.98  --prep_unflatten                        true
% 3.03/0.98  --prep_res_sim                          true
% 3.03/0.98  --prep_upred                            true
% 3.03/0.98  --prep_sem_filter                       exhaustive
% 3.03/0.98  --prep_sem_filter_out                   false
% 3.03/0.98  --pred_elim                             true
% 3.03/0.98  --res_sim_input                         true
% 3.03/0.98  --eq_ax_congr_red                       true
% 3.03/0.98  --pure_diseq_elim                       true
% 3.03/0.98  --brand_transform                       false
% 3.03/0.98  --non_eq_to_eq                          false
% 3.03/0.98  --prep_def_merge                        true
% 3.03/0.98  --prep_def_merge_prop_impl              false
% 3.03/0.98  --prep_def_merge_mbd                    true
% 3.03/0.98  --prep_def_merge_tr_red                 false
% 3.03/0.98  --prep_def_merge_tr_cl                  false
% 3.03/0.98  --smt_preprocessing                     true
% 3.03/0.98  --smt_ac_axioms                         fast
% 3.03/0.98  --preprocessed_out                      false
% 3.03/0.98  --preprocessed_stats                    false
% 3.03/0.98  
% 3.03/0.98  ------ Abstraction refinement Options
% 3.03/0.98  
% 3.03/0.98  --abstr_ref                             []
% 3.03/0.98  --abstr_ref_prep                        false
% 3.03/0.98  --abstr_ref_until_sat                   false
% 3.03/0.98  --abstr_ref_sig_restrict                funpre
% 3.03/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.98  --abstr_ref_under                       []
% 3.03/0.98  
% 3.03/0.98  ------ SAT Options
% 3.03/0.98  
% 3.03/0.98  --sat_mode                              false
% 3.03/0.98  --sat_fm_restart_options                ""
% 3.03/0.99  --sat_gr_def                            false
% 3.03/0.99  --sat_epr_types                         true
% 3.03/0.99  --sat_non_cyclic_types                  false
% 3.03/0.99  --sat_finite_models                     false
% 3.03/0.99  --sat_fm_lemmas                         false
% 3.03/0.99  --sat_fm_prep                           false
% 3.03/0.99  --sat_fm_uc_incr                        true
% 3.03/0.99  --sat_out_model                         small
% 3.03/0.99  --sat_out_clauses                       false
% 3.03/0.99  
% 3.03/0.99  ------ QBF Options
% 3.03/0.99  
% 3.03/0.99  --qbf_mode                              false
% 3.03/0.99  --qbf_elim_univ                         false
% 3.03/0.99  --qbf_dom_inst                          none
% 3.03/0.99  --qbf_dom_pre_inst                      false
% 3.03/0.99  --qbf_sk_in                             false
% 3.03/0.99  --qbf_pred_elim                         true
% 3.03/0.99  --qbf_split                             512
% 3.03/0.99  
% 3.03/0.99  ------ BMC1 Options
% 3.03/0.99  
% 3.03/0.99  --bmc1_incremental                      false
% 3.03/0.99  --bmc1_axioms                           reachable_all
% 3.03/0.99  --bmc1_min_bound                        0
% 3.03/0.99  --bmc1_max_bound                        -1
% 3.03/0.99  --bmc1_max_bound_default                -1
% 3.03/0.99  --bmc1_symbol_reachability              true
% 3.03/0.99  --bmc1_property_lemmas                  false
% 3.03/0.99  --bmc1_k_induction                      false
% 3.03/0.99  --bmc1_non_equiv_states                 false
% 3.03/0.99  --bmc1_deadlock                         false
% 3.03/0.99  --bmc1_ucm                              false
% 3.03/0.99  --bmc1_add_unsat_core                   none
% 3.03/0.99  --bmc1_unsat_core_children              false
% 3.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.99  --bmc1_out_stat                         full
% 3.03/0.99  --bmc1_ground_init                      false
% 3.03/0.99  --bmc1_pre_inst_next_state              false
% 3.03/0.99  --bmc1_pre_inst_state                   false
% 3.03/0.99  --bmc1_pre_inst_reach_state             false
% 3.03/0.99  --bmc1_out_unsat_core                   false
% 3.03/0.99  --bmc1_aig_witness_out                  false
% 3.03/0.99  --bmc1_verbose                          false
% 3.03/0.99  --bmc1_dump_clauses_tptp                false
% 3.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.99  --bmc1_dump_file                        -
% 3.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.99  --bmc1_ucm_extend_mode                  1
% 3.03/0.99  --bmc1_ucm_init_mode                    2
% 3.03/0.99  --bmc1_ucm_cone_mode                    none
% 3.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.99  --bmc1_ucm_relax_model                  4
% 3.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.99  --bmc1_ucm_layered_model                none
% 3.03/0.99  --bmc1_ucm_max_lemma_size               10
% 3.03/0.99  
% 3.03/0.99  ------ AIG Options
% 3.03/0.99  
% 3.03/0.99  --aig_mode                              false
% 3.03/0.99  
% 3.03/0.99  ------ Instantiation Options
% 3.03/0.99  
% 3.03/0.99  --instantiation_flag                    true
% 3.03/0.99  --inst_sos_flag                         false
% 3.03/0.99  --inst_sos_phase                        true
% 3.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel_side                     none
% 3.03/0.99  --inst_solver_per_active                1400
% 3.03/0.99  --inst_solver_calls_frac                1.
% 3.03/0.99  --inst_passive_queue_type               priority_queues
% 3.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.99  --inst_passive_queues_freq              [25;2]
% 3.03/0.99  --inst_dismatching                      true
% 3.03/0.99  --inst_eager_unprocessed_to_passive     true
% 3.03/0.99  --inst_prop_sim_given                   true
% 3.03/0.99  --inst_prop_sim_new                     false
% 3.03/0.99  --inst_subs_new                         false
% 3.03/0.99  --inst_eq_res_simp                      false
% 3.03/0.99  --inst_subs_given                       false
% 3.03/0.99  --inst_orphan_elimination               true
% 3.03/0.99  --inst_learning_loop_flag               true
% 3.03/0.99  --inst_learning_start                   3000
% 3.03/0.99  --inst_learning_factor                  2
% 3.03/0.99  --inst_start_prop_sim_after_learn       3
% 3.03/0.99  --inst_sel_renew                        solver
% 3.03/0.99  --inst_lit_activity_flag                true
% 3.03/0.99  --inst_restr_to_given                   false
% 3.03/0.99  --inst_activity_threshold               500
% 3.03/0.99  --inst_out_proof                        true
% 3.03/0.99  
% 3.03/0.99  ------ Resolution Options
% 3.03/0.99  
% 3.03/0.99  --resolution_flag                       false
% 3.03/0.99  --res_lit_sel                           adaptive
% 3.03/0.99  --res_lit_sel_side                      none
% 3.03/0.99  --res_ordering                          kbo
% 3.03/0.99  --res_to_prop_solver                    active
% 3.03/0.99  --res_prop_simpl_new                    false
% 3.03/0.99  --res_prop_simpl_given                  true
% 3.03/0.99  --res_passive_queue_type                priority_queues
% 3.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.99  --res_passive_queues_freq               [15;5]
% 3.03/0.99  --res_forward_subs                      full
% 3.03/0.99  --res_backward_subs                     full
% 3.03/0.99  --res_forward_subs_resolution           true
% 3.03/0.99  --res_backward_subs_resolution          true
% 3.03/0.99  --res_orphan_elimination                true
% 3.03/0.99  --res_time_limit                        2.
% 3.03/0.99  --res_out_proof                         true
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Options
% 3.03/0.99  
% 3.03/0.99  --superposition_flag                    true
% 3.03/0.99  --sup_passive_queue_type                priority_queues
% 3.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.99  --demod_completeness_check              fast
% 3.03/0.99  --demod_use_ground                      true
% 3.03/0.99  --sup_to_prop_solver                    passive
% 3.03/0.99  --sup_prop_simpl_new                    true
% 3.03/0.99  --sup_prop_simpl_given                  true
% 3.03/0.99  --sup_fun_splitting                     false
% 3.03/0.99  --sup_smt_interval                      50000
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Simplification Setup
% 3.03/0.99  
% 3.03/0.99  --sup_indices_passive                   []
% 3.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_full_bw                           [BwDemod]
% 3.03/0.99  --sup_immed_triv                        [TrivRules]
% 3.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_immed_bw_main                     []
% 3.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  
% 3.03/0.99  ------ Combination Options
% 3.03/0.99  
% 3.03/0.99  --comb_res_mult                         3
% 3.03/0.99  --comb_sup_mult                         2
% 3.03/0.99  --comb_inst_mult                        10
% 3.03/0.99  
% 3.03/0.99  ------ Debug Options
% 3.03/0.99  
% 3.03/0.99  --dbg_backtrace                         false
% 3.03/0.99  --dbg_dump_prop_clauses                 false
% 3.03/0.99  --dbg_dump_prop_clauses_file            -
% 3.03/0.99  --dbg_out_stat                          false
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  ------ Proving...
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS status Theorem for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  fof(f5,axiom,(
% 3.03/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f14,plain,(
% 3.03/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f5])).
% 3.03/0.99  
% 3.03/0.99  fof(f15,plain,(
% 3.03/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.99    inference(flattening,[],[f14])).
% 3.03/0.99  
% 3.03/0.99  fof(f26,plain,(
% 3.03/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.99    inference(nnf_transformation,[],[f15])).
% 3.03/0.99  
% 3.03/0.99  fof(f27,plain,(
% 3.03/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.99    inference(rectify,[],[f26])).
% 3.03/0.99  
% 3.03/0.99  fof(f30,plain,(
% 3.03/0.99    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f29,plain,(
% 3.03/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f28,plain,(
% 3.03/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f31,plain,(
% 3.03/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).
% 3.03/0.99  
% 3.03/0.99  fof(f43,plain,(
% 3.03/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f31])).
% 3.03/0.99  
% 3.03/0.99  fof(f60,plain,(
% 3.03/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(equality_resolution,[],[f43])).
% 3.03/0.99  
% 3.03/0.99  fof(f9,conjecture,(
% 3.03/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f10,negated_conjecture,(
% 3.03/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.03/0.99    inference(negated_conjecture,[],[f9])).
% 3.03/0.99  
% 3.03/0.99  fof(f11,plain,(
% 3.03/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.03/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.03/0.99  
% 3.03/0.99  fof(f19,plain,(
% 3.03/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.03/0.99    inference(ennf_transformation,[],[f11])).
% 3.03/0.99  
% 3.03/0.99  fof(f20,plain,(
% 3.03/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.03/0.99    inference(flattening,[],[f19])).
% 3.03/0.99  
% 3.03/0.99  fof(f33,plain,(
% 3.03/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f32,plain,(
% 3.03/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f34,plain,(
% 3.03/0.99    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7)),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f20,f33,f32])).
% 3.03/0.99  
% 3.03/0.99  fof(f53,plain,(
% 3.03/0.99    v1_funct_1(sK7)),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f42,plain,(
% 3.03/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f31])).
% 3.03/0.99  
% 3.03/0.99  fof(f61,plain,(
% 3.03/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(equality_resolution,[],[f42])).
% 3.03/0.99  
% 3.03/0.99  fof(f1,axiom,(
% 3.03/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f12,plain,(
% 3.03/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.03/0.99    inference(ennf_transformation,[],[f1])).
% 3.03/0.99  
% 3.03/0.99  fof(f21,plain,(
% 3.03/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/0.99    inference(nnf_transformation,[],[f12])).
% 3.03/0.99  
% 3.03/0.99  fof(f22,plain,(
% 3.03/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/0.99    inference(rectify,[],[f21])).
% 3.03/0.99  
% 3.03/0.99  fof(f23,plain,(
% 3.03/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.03/0.99    introduced(choice_axiom,[])).
% 3.03/0.99  
% 3.03/0.99  fof(f24,plain,(
% 3.03/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 3.03/0.99  
% 3.03/0.99  fof(f35,plain,(
% 3.03/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f24])).
% 3.03/0.99  
% 3.03/0.99  fof(f54,plain,(
% 3.03/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f2,axiom,(
% 3.03/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f25,plain,(
% 3.03/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.03/0.99    inference(nnf_transformation,[],[f2])).
% 3.03/0.99  
% 3.03/0.99  fof(f38,plain,(
% 3.03/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f25])).
% 3.03/0.99  
% 3.03/0.99  fof(f3,axiom,(
% 3.03/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f13,plain,(
% 3.03/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.03/0.99    inference(ennf_transformation,[],[f3])).
% 3.03/0.99  
% 3.03/0.99  fof(f40,plain,(
% 3.03/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f13])).
% 3.03/0.99  
% 3.03/0.99  fof(f39,plain,(
% 3.03/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f25])).
% 3.03/0.99  
% 3.03/0.99  fof(f4,axiom,(
% 3.03/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f41,plain,(
% 3.03/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f4])).
% 3.03/0.99  
% 3.03/0.99  fof(f8,axiom,(
% 3.03/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f18,plain,(
% 3.03/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(ennf_transformation,[],[f8])).
% 3.03/0.99  
% 3.03/0.99  fof(f52,plain,(
% 3.03/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f18])).
% 3.03/0.99  
% 3.03/0.99  fof(f55,plain,(
% 3.03/0.99    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f44,plain,(
% 3.03/0.99    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f31])).
% 3.03/0.99  
% 3.03/0.99  fof(f59,plain,(
% 3.03/0.99    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/0.99    inference(equality_resolution,[],[f44])).
% 3.03/0.99  
% 3.03/0.99  fof(f56,plain,(
% 3.03/0.99    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 3.03/0.99    inference(cnf_transformation,[],[f34])).
% 3.03/0.99  
% 3.03/0.99  fof(f7,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f17,plain,(
% 3.03/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(ennf_transformation,[],[f7])).
% 3.03/0.99  
% 3.03/0.99  fof(f51,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f17])).
% 3.03/0.99  
% 3.03/0.99  fof(f6,axiom,(
% 3.03/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.03/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.99  
% 3.03/0.99  fof(f16,plain,(
% 3.03/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/0.99    inference(ennf_transformation,[],[f6])).
% 3.03/0.99  
% 3.03/0.99  fof(f50,plain,(
% 3.03/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/0.99    inference(cnf_transformation,[],[f16])).
% 3.03/0.99  
% 3.03/0.99  cnf(c_13,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.03/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.03/0.99      | ~ v1_funct_1(X1)
% 3.03/0.99      | ~ v1_relat_1(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_21,negated_conjecture,
% 3.03/0.99      ( v1_funct_1(sK7) ),
% 3.03/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_529,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.03/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.03/0.99      | ~ v1_relat_1(X1)
% 3.03/0.99      | sK7 != X1 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_530,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.03/0.99      | r2_hidden(sK3(sK7,X1,X0),X1)
% 3.03/0.99      | ~ v1_relat_1(sK7) ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_529]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1414,plain,
% 3.03/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.03/0.99      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 3.03/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_14,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.03/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.03/0.99      | ~ v1_funct_1(X1)
% 3.03/0.99      | ~ v1_relat_1(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_514,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.03/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.03/0.99      | ~ v1_relat_1(X1)
% 3.03/0.99      | sK7 != X1 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_515,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.03/0.99      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7))
% 3.03/0.99      | ~ v1_relat_1(sK7) ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_514]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1415,plain,
% 3.03/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.03/0.99      | r2_hidden(sK3(sK7,X1,X0),k1_relat_1(sK7)) = iProver_top
% 3.03/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.03/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1431,plain,
% 3.03/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.03/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.03/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2827,plain,
% 3.03/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.03/0.99      | r2_hidden(sK3(sK7,X1,X0),X2) = iProver_top
% 3.03/0.99      | r1_tarski(k1_relat_1(sK7),X2) != iProver_top
% 3.03/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1415,c_1431]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_20,negated_conjecture,
% 3.03/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.03/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1422,plain,
% 3.03/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1429,plain,
% 3.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.03/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1830,plain,
% 3.03/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1422,c_1429]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_5,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.03/0.99      | ~ v1_relat_1(X1)
% 3.03/0.99      | v1_relat_1(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3,plain,
% 3.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_175,plain,
% 3.03/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.03/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_176,plain,
% 3.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.03/0.99      inference(renaming,[status(thm)],[c_175]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_220,plain,
% 3.03/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.03/0.99      inference(bin_hyper_res,[status(thm)],[c_5,c_176]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1656,plain,
% 3.03/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.03/0.99      | v1_relat_1(X0)
% 3.03/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_220]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2035,plain,
% 3.03/0.99      ( ~ r1_tarski(sK7,k2_zfmisc_1(sK4,sK5))
% 3.03/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 3.03/0.99      | v1_relat_1(sK7) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_1656]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2037,plain,
% 3.03/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.03/0.99      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.03/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2035]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_6,plain,
% 3.03/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2676,plain,
% 3.03/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2677,plain,
% 3.03/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2676]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4760,plain,
% 3.03/0.99      ( r1_tarski(k1_relat_1(sK7),X2) != iProver_top
% 3.03/0.99      | r2_hidden(sK3(sK7,X1,X0),X2) = iProver_top
% 3.03/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_2827,c_1830,c_2037,c_2677]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4761,plain,
% 3.03/0.99      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.03/0.99      | r2_hidden(sK3(sK7,X1,X0),X2) = iProver_top
% 3.03/0.99      | r1_tarski(k1_relat_1(sK7),X2) != iProver_top ),
% 3.03/0.99      inference(renaming,[status(thm)],[c_4760]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_17,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.03/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1425,plain,
% 3.03/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.03/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2566,plain,
% 3.03/0.99      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1422,c_1425]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_19,negated_conjecture,
% 3.03/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1423,plain,
% 3.03/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2949,plain,
% 3.03/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.03/0.99      inference(demodulation,[status(thm)],[c_2566,c_1423]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_12,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.03/0.99      | ~ v1_funct_1(X1)
% 3.03/0.99      | ~ v1_relat_1(X1)
% 3.03/0.99      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 3.03/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_544,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.03/0.99      | ~ v1_relat_1(X1)
% 3.03/0.99      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
% 3.03/0.99      | sK7 != X1 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_545,plain,
% 3.03/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 3.03/0.99      | ~ v1_relat_1(sK7)
% 3.03/0.99      | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_544]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1413,plain,
% 3.03/0.99      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 3.03/0.99      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.03/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3000,plain,
% 3.03/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
% 3.03/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_2949,c_1413]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3073,plain,
% 3.03/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_3000,c_1830,c_2037,c_2677]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_18,negated_conjecture,
% 3.03/0.99      ( ~ r2_hidden(X0,sK4)
% 3.03/0.99      | ~ r2_hidden(X0,sK6)
% 3.03/0.99      | k1_funct_1(sK7,X0) != sK8 ),
% 3.03/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1424,plain,
% 3.03/0.99      ( k1_funct_1(sK7,X0) != sK8
% 3.03/0.99      | r2_hidden(X0,sK4) != iProver_top
% 3.03/0.99      | r2_hidden(X0,sK6) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3077,plain,
% 3.03/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
% 3.03/0.99      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_3073,c_1424]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4776,plain,
% 3.03/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 3.03/0.99      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.03/0.99      | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_4761,c_3077]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_16,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1426,plain,
% 3.03/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.03/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2699,plain,
% 3.03/0.99      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1422,c_1426]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_15,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.03/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1427,plain,
% 3.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.03/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_2946,plain,
% 3.03/0.99      ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4)) = iProver_top
% 3.03/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_2699,c_1427]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_23,plain,
% 3.03/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3206,plain,
% 3.03/0.99      ( m1_subset_1(k1_relat_1(sK7),k1_zfmisc_1(sK4)) = iProver_top ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_2946,c_23]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_3211,plain,
% 3.03/0.99      ( r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_3206,c_1429]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4857,plain,
% 3.03/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_4776,c_2949,c_3211]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_4862,plain,
% 3.03/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.03/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1414,c_4857]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(contradiction,plain,
% 3.03/0.99      ( $false ),
% 3.03/0.99      inference(minisat,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_4862,c_2949,c_2677,c_2037,c_1830]) ).
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  ------                               Statistics
% 3.03/0.99  
% 3.03/0.99  ------ General
% 3.03/0.99  
% 3.03/0.99  abstr_ref_over_cycles:                  0
% 3.03/0.99  abstr_ref_under_cycles:                 0
% 3.03/0.99  gc_basic_clause_elim:                   0
% 3.03/0.99  forced_gc_time:                         0
% 3.03/0.99  parsing_time:                           0.009
% 3.03/0.99  unif_index_cands_time:                  0.
% 3.03/0.99  unif_index_add_time:                    0.
% 3.03/0.99  orderings_time:                         0.
% 3.03/0.99  out_proof_time:                         0.01
% 3.03/0.99  total_time:                             0.216
% 3.03/0.99  num_of_symbols:                         52
% 3.03/0.99  num_of_terms:                           4333
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing
% 3.03/0.99  
% 3.03/0.99  num_of_splits:                          0
% 3.03/0.99  num_of_split_atoms:                     0
% 3.03/0.99  num_of_reused_defs:                     0
% 3.03/0.99  num_eq_ax_congr_red:                    47
% 3.03/0.99  num_of_sem_filtered_clauses:            1
% 3.03/0.99  num_of_subtypes:                        0
% 3.03/0.99  monotx_restored_types:                  0
% 3.03/0.99  sat_num_of_epr_types:                   0
% 3.03/0.99  sat_num_of_non_cyclic_types:            0
% 3.03/0.99  sat_guarded_non_collapsed_types:        0
% 3.03/0.99  num_pure_diseq_elim:                    0
% 3.03/0.99  simp_replaced_by:                       0
% 3.03/0.99  res_preprocessed:                       114
% 3.03/0.99  prep_upred:                             0
% 3.03/0.99  prep_unflattend:                        20
% 3.03/0.99  smt_new_axioms:                         0
% 3.03/0.99  pred_elim_cands:                        4
% 3.03/0.99  pred_elim:                              1
% 3.03/0.99  pred_elim_cl:                           1
% 3.03/0.99  pred_elim_cycles:                       4
% 3.03/0.99  merged_defs:                            8
% 3.03/0.99  merged_defs_ncl:                        0
% 3.03/0.99  bin_hyper_res:                          9
% 3.03/0.99  prep_cycles:                            4
% 3.03/0.99  pred_elim_time:                         0.006
% 3.03/0.99  splitting_time:                         0.
% 3.03/0.99  sem_filter_time:                        0.
% 3.03/0.99  monotx_time:                            0.
% 3.03/0.99  subtype_inf_time:                       0.
% 3.03/0.99  
% 3.03/0.99  ------ Problem properties
% 3.03/0.99  
% 3.03/0.99  clauses:                                21
% 3.03/0.99  conjectures:                            3
% 3.03/0.99  epr:                                    2
% 3.03/0.99  horn:                                   17
% 3.03/0.99  ground:                                 2
% 3.03/0.99  unary:                                  3
% 3.03/0.99  binary:                                 7
% 3.03/0.99  lits:                                   57
% 3.03/0.99  lits_eq:                                10
% 3.03/0.99  fd_pure:                                0
% 3.03/0.99  fd_pseudo:                              0
% 3.03/0.99  fd_cond:                                0
% 3.03/0.99  fd_pseudo_cond:                         4
% 3.03/0.99  ac_symbols:                             0
% 3.03/0.99  
% 3.03/0.99  ------ Propositional Solver
% 3.03/0.99  
% 3.03/0.99  prop_solver_calls:                      29
% 3.03/0.99  prop_fast_solver_calls:                 864
% 3.03/0.99  smt_solver_calls:                       0
% 3.03/0.99  smt_fast_solver_calls:                  0
% 3.03/0.99  prop_num_of_clauses:                    1523
% 3.03/0.99  prop_preprocess_simplified:             5149
% 3.03/0.99  prop_fo_subsumed:                       15
% 3.03/0.99  prop_solver_time:                       0.
% 3.03/0.99  smt_solver_time:                        0.
% 3.03/0.99  smt_fast_solver_time:                   0.
% 3.03/0.99  prop_fast_solver_time:                  0.
% 3.03/0.99  prop_unsat_core_time:                   0.
% 3.03/0.99  
% 3.03/0.99  ------ QBF
% 3.03/0.99  
% 3.03/0.99  qbf_q_res:                              0
% 3.03/0.99  qbf_num_tautologies:                    0
% 3.03/0.99  qbf_prep_cycles:                        0
% 3.03/0.99  
% 3.03/0.99  ------ BMC1
% 3.03/0.99  
% 3.03/0.99  bmc1_current_bound:                     -1
% 3.03/0.99  bmc1_last_solved_bound:                 -1
% 3.03/0.99  bmc1_unsat_core_size:                   -1
% 3.03/0.99  bmc1_unsat_core_parents_size:           -1
% 3.03/0.99  bmc1_merge_next_fun:                    0
% 3.03/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.03/0.99  
% 3.03/0.99  ------ Instantiation
% 3.03/0.99  
% 3.03/0.99  inst_num_of_clauses:                    398
% 3.03/0.99  inst_num_in_passive:                    118
% 3.03/0.99  inst_num_in_active:                     193
% 3.03/0.99  inst_num_in_unprocessed:                87
% 3.03/0.99  inst_num_of_loops:                      260
% 3.03/0.99  inst_num_of_learning_restarts:          0
% 3.03/0.99  inst_num_moves_active_passive:          63
% 3.03/0.99  inst_lit_activity:                      0
% 3.03/0.99  inst_lit_activity_moves:                0
% 3.03/0.99  inst_num_tautologies:                   0
% 3.03/0.99  inst_num_prop_implied:                  0
% 3.03/0.99  inst_num_existing_simplified:           0
% 3.03/0.99  inst_num_eq_res_simplified:             0
% 3.03/0.99  inst_num_child_elim:                    0
% 3.03/0.99  inst_num_of_dismatching_blockings:      147
% 3.03/0.99  inst_num_of_non_proper_insts:           323
% 3.03/0.99  inst_num_of_duplicates:                 0
% 3.03/0.99  inst_inst_num_from_inst_to_res:         0
% 3.03/0.99  inst_dismatching_checking_time:         0.
% 3.03/0.99  
% 3.03/0.99  ------ Resolution
% 3.03/0.99  
% 3.03/0.99  res_num_of_clauses:                     0
% 3.03/0.99  res_num_in_passive:                     0
% 3.03/0.99  res_num_in_active:                      0
% 3.03/0.99  res_num_of_loops:                       118
% 3.03/0.99  res_forward_subset_subsumed:            17
% 3.03/0.99  res_backward_subset_subsumed:           2
% 3.03/0.99  res_forward_subsumed:                   0
% 3.03/0.99  res_backward_subsumed:                  0
% 3.03/0.99  res_forward_subsumption_resolution:     0
% 3.03/0.99  res_backward_subsumption_resolution:    0
% 3.03/0.99  res_clause_to_clause_subsumption:       311
% 3.03/0.99  res_orphan_elimination:                 0
% 3.03/0.99  res_tautology_del:                      58
% 3.03/0.99  res_num_eq_res_simplified:              0
% 3.03/0.99  res_num_sel_changes:                    0
% 3.03/0.99  res_moves_from_active_to_pass:          0
% 3.03/0.99  
% 3.03/0.99  ------ Superposition
% 3.03/0.99  
% 3.03/0.99  sup_time_total:                         0.
% 3.03/0.99  sup_time_generating:                    0.
% 3.03/0.99  sup_time_sim_full:                      0.
% 3.03/0.99  sup_time_sim_immed:                     0.
% 3.03/0.99  
% 3.03/0.99  sup_num_of_clauses:                     122
% 3.03/0.99  sup_num_in_active:                      50
% 3.03/0.99  sup_num_in_passive:                     72
% 3.03/0.99  sup_num_of_loops:                       51
% 3.03/0.99  sup_fw_superposition:                   66
% 3.03/0.99  sup_bw_superposition:                   52
% 3.03/0.99  sup_immediate_simplified:               7
% 3.03/0.99  sup_given_eliminated:                   0
% 3.03/0.99  comparisons_done:                       0
% 3.03/0.99  comparisons_avoided:                    4
% 3.03/0.99  
% 3.03/0.99  ------ Simplifications
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  sim_fw_subset_subsumed:                 2
% 3.03/0.99  sim_bw_subset_subsumed:                 1
% 3.03/0.99  sim_fw_subsumed:                        2
% 3.03/0.99  sim_bw_subsumed:                        2
% 3.03/0.99  sim_fw_subsumption_res:                 0
% 3.03/0.99  sim_bw_subsumption_res:                 0
% 3.03/0.99  sim_tautology_del:                      2
% 3.03/0.99  sim_eq_tautology_del:                   1
% 3.03/0.99  sim_eq_res_simp:                        0
% 3.03/0.99  sim_fw_demodulated:                     1
% 3.03/0.99  sim_bw_demodulated:                     1
% 3.03/0.99  sim_light_normalised:                   3
% 3.03/0.99  sim_joinable_taut:                      0
% 3.03/0.99  sim_joinable_simp:                      0
% 3.03/0.99  sim_ac_normalised:                      0
% 3.03/0.99  sim_smt_subsumption:                    0
% 3.03/0.99  
%------------------------------------------------------------------------------
