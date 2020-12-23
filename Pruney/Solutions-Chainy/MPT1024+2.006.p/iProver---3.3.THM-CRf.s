%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:48 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 705 expanded)
%              Number of clauses        :   91 ( 240 expanded)
%              Number of leaves         :   19 ( 168 expanded)
%              Depth                    :   26
%              Number of atoms          :  600 (3570 expanded)
%              Number of equality atoms :  268 ( 926 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
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

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ r2_hidden(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f32,f50,f49])).

fof(f85,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f51])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f91,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f84,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f29])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f54])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1339,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_464,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_465,plain,
    ( k7_relset_1(X0,X1,sK7,X2) = k9_relat_1(sK7,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_1543,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(equality_resolution,[status(thm)],[c_465])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1337,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1573,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1543,c_1337])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1340,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_745,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_746,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_745])).

cnf(c_1325,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_747,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_997,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1554,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_482,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_483,plain,
    ( v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1557,plain,
    ( v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_1558,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_1951,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | k1_funct_1(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1325,c_747,c_1554,c_1558])).

cnf(c_1952,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_1951])).

cnf(c_2746,plain,
    ( k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1952])).

cnf(c_2827,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2746,c_1554,c_1558])).

cnf(c_2828,plain,
    ( k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2827])).

cnf(c_2839,plain,
    ( k1_funct_1(sK7,sK0(sK8,sK6,sK7)) = sK8 ),
    inference(superposition,[status(thm)],[c_1573,c_2828])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_709,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_710,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_1327,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_711,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_2499,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_711,c_1554,c_1558])).

cnf(c_2500,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2499])).

cnf(c_2878,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2839,c_2500])).

cnf(c_2941,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_2878])).

cnf(c_3430,plain,
    ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2941,c_1554,c_1558,c_1573])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_428,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_33])).

cnf(c_429,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | k1_relset_1(X0,X1,sK7) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_808,plain,
    ( k1_relset_1(X0,X1,sK7) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK5 != X1
    | sK4 != X0
    | sK7 != sK7
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_429])).

cnf(c_809,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_808])).

cnf(c_881,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_809])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_473,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_474,plain,
    ( k1_relset_1(X0,X1,sK7) = k1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1540,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(equality_resolution,[status(thm)],[c_474])).

cnf(c_1649,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_881,c_1540])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_613,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_35])).

cnf(c_614,plain,
    ( r2_hidden(sK2(sK7,X0),k1_relat_1(sK7))
    | r2_hidden(sK1(sK7,X0),X0)
    | ~ v1_relat_1(sK7)
    | k2_relat_1(sK7) = X0 ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_1333,plain,
    ( k2_relat_1(sK7) = X0
    | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(sK7,X0),X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_615,plain,
    ( k2_relat_1(sK7) = X0
    | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(sK7,X0),X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_2551,plain,
    ( r2_hidden(sK1(sK7,X0),X0) = iProver_top
    | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | k2_relat_1(sK7) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1333,c_615,c_1554,c_1558])).

cnf(c_2552,plain,
    ( k2_relat_1(sK7) = X0
    | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(sK7,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2551])).

cnf(c_2560,plain,
    ( k2_relat_1(sK7) = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK2(sK7,X0),sK4) = iProver_top
    | r2_hidden(sK1(sK7,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_2552])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1341,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2660,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1339])).

cnf(c_3441,plain,
    ( r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2660,c_1554,c_1558])).

cnf(c_3442,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3441])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1338,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2879,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),sK4) != iProver_top
    | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2839,c_1338])).

cnf(c_3450,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3442,c_2879])).

cnf(c_3912,plain,
    ( r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3450,c_1573])).

cnf(c_3913,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3912])).

cnf(c_3918,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_3913])).

cnf(c_3964,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2560,c_1554,c_1558,c_1573,c_3918])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_378,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_5])).

cnf(c_388,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_378,c_21])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X0 != X4
    | k2_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_388,c_20])).

cnf(c_399,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_559,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_399])).

cnf(c_560,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1334,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r2_hidden(X1,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_1878,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1334])).

cnf(c_3969,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3964,c_1878])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4029,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3969,c_0])).

cnf(c_4030,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4029])).

cnf(c_4607,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3430,c_4030])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.02/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.03  
% 3.02/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/1.03  
% 3.02/1.03  ------  iProver source info
% 3.02/1.03  
% 3.02/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.02/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/1.03  git: non_committed_changes: false
% 3.02/1.03  git: last_make_outside_of_git: false
% 3.02/1.03  
% 3.02/1.03  ------ 
% 3.02/1.03  
% 3.02/1.03  ------ Input Options
% 3.02/1.03  
% 3.02/1.03  --out_options                           all
% 3.02/1.03  --tptp_safe_out                         true
% 3.02/1.03  --problem_path                          ""
% 3.02/1.03  --include_path                          ""
% 3.02/1.03  --clausifier                            res/vclausify_rel
% 3.02/1.03  --clausifier_options                    --mode clausify
% 3.02/1.03  --stdin                                 false
% 3.02/1.03  --stats_out                             all
% 3.02/1.03  
% 3.02/1.03  ------ General Options
% 3.02/1.03  
% 3.02/1.03  --fof                                   false
% 3.02/1.03  --time_out_real                         305.
% 3.02/1.03  --time_out_virtual                      -1.
% 3.02/1.03  --symbol_type_check                     false
% 3.02/1.03  --clausify_out                          false
% 3.02/1.03  --sig_cnt_out                           false
% 3.02/1.03  --trig_cnt_out                          false
% 3.02/1.03  --trig_cnt_out_tolerance                1.
% 3.02/1.03  --trig_cnt_out_sk_spl                   false
% 3.02/1.03  --abstr_cl_out                          false
% 3.02/1.03  
% 3.02/1.03  ------ Global Options
% 3.02/1.03  
% 3.02/1.03  --schedule                              default
% 3.02/1.03  --add_important_lit                     false
% 3.02/1.03  --prop_solver_per_cl                    1000
% 3.02/1.03  --min_unsat_core                        false
% 3.02/1.03  --soft_assumptions                      false
% 3.02/1.03  --soft_lemma_size                       3
% 3.02/1.03  --prop_impl_unit_size                   0
% 3.02/1.03  --prop_impl_unit                        []
% 3.02/1.03  --share_sel_clauses                     true
% 3.02/1.03  --reset_solvers                         false
% 3.02/1.03  --bc_imp_inh                            [conj_cone]
% 3.02/1.03  --conj_cone_tolerance                   3.
% 3.02/1.03  --extra_neg_conj                        none
% 3.02/1.03  --large_theory_mode                     true
% 3.02/1.03  --prolific_symb_bound                   200
% 3.02/1.03  --lt_threshold                          2000
% 3.02/1.03  --clause_weak_htbl                      true
% 3.02/1.03  --gc_record_bc_elim                     false
% 3.02/1.03  
% 3.02/1.03  ------ Preprocessing Options
% 3.02/1.03  
% 3.02/1.03  --preprocessing_flag                    true
% 3.02/1.03  --time_out_prep_mult                    0.1
% 3.02/1.03  --splitting_mode                        input
% 3.02/1.03  --splitting_grd                         true
% 3.02/1.03  --splitting_cvd                         false
% 3.02/1.03  --splitting_cvd_svl                     false
% 3.02/1.03  --splitting_nvd                         32
% 3.02/1.03  --sub_typing                            true
% 3.02/1.03  --prep_gs_sim                           true
% 3.02/1.03  --prep_unflatten                        true
% 3.02/1.03  --prep_res_sim                          true
% 3.02/1.03  --prep_upred                            true
% 3.02/1.03  --prep_sem_filter                       exhaustive
% 3.02/1.03  --prep_sem_filter_out                   false
% 3.02/1.03  --pred_elim                             true
% 3.02/1.03  --res_sim_input                         true
% 3.02/1.03  --eq_ax_congr_red                       true
% 3.02/1.03  --pure_diseq_elim                       true
% 3.02/1.03  --brand_transform                       false
% 3.02/1.03  --non_eq_to_eq                          false
% 3.02/1.03  --prep_def_merge                        true
% 3.02/1.03  --prep_def_merge_prop_impl              false
% 3.02/1.03  --prep_def_merge_mbd                    true
% 3.02/1.03  --prep_def_merge_tr_red                 false
% 3.02/1.03  --prep_def_merge_tr_cl                  false
% 3.02/1.03  --smt_preprocessing                     true
% 3.02/1.03  --smt_ac_axioms                         fast
% 3.02/1.03  --preprocessed_out                      false
% 3.02/1.03  --preprocessed_stats                    false
% 3.02/1.03  
% 3.02/1.03  ------ Abstraction refinement Options
% 3.02/1.03  
% 3.02/1.03  --abstr_ref                             []
% 3.02/1.03  --abstr_ref_prep                        false
% 3.02/1.03  --abstr_ref_until_sat                   false
% 3.02/1.03  --abstr_ref_sig_restrict                funpre
% 3.02/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.03  --abstr_ref_under                       []
% 3.02/1.03  
% 3.02/1.03  ------ SAT Options
% 3.02/1.03  
% 3.02/1.03  --sat_mode                              false
% 3.02/1.03  --sat_fm_restart_options                ""
% 3.02/1.03  --sat_gr_def                            false
% 3.02/1.03  --sat_epr_types                         true
% 3.02/1.03  --sat_non_cyclic_types                  false
% 3.02/1.03  --sat_finite_models                     false
% 3.02/1.03  --sat_fm_lemmas                         false
% 3.02/1.03  --sat_fm_prep                           false
% 3.02/1.03  --sat_fm_uc_incr                        true
% 3.02/1.03  --sat_out_model                         small
% 3.02/1.03  --sat_out_clauses                       false
% 3.02/1.03  
% 3.02/1.03  ------ QBF Options
% 3.02/1.03  
% 3.02/1.03  --qbf_mode                              false
% 3.02/1.03  --qbf_elim_univ                         false
% 3.02/1.03  --qbf_dom_inst                          none
% 3.02/1.03  --qbf_dom_pre_inst                      false
% 3.02/1.03  --qbf_sk_in                             false
% 3.02/1.03  --qbf_pred_elim                         true
% 3.02/1.03  --qbf_split                             512
% 3.02/1.03  
% 3.02/1.03  ------ BMC1 Options
% 3.02/1.03  
% 3.02/1.03  --bmc1_incremental                      false
% 3.02/1.03  --bmc1_axioms                           reachable_all
% 3.02/1.03  --bmc1_min_bound                        0
% 3.02/1.03  --bmc1_max_bound                        -1
% 3.02/1.03  --bmc1_max_bound_default                -1
% 3.02/1.03  --bmc1_symbol_reachability              true
% 3.02/1.03  --bmc1_property_lemmas                  false
% 3.02/1.03  --bmc1_k_induction                      false
% 3.02/1.03  --bmc1_non_equiv_states                 false
% 3.02/1.03  --bmc1_deadlock                         false
% 3.02/1.03  --bmc1_ucm                              false
% 3.02/1.03  --bmc1_add_unsat_core                   none
% 3.02/1.03  --bmc1_unsat_core_children              false
% 3.02/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.03  --bmc1_out_stat                         full
% 3.02/1.03  --bmc1_ground_init                      false
% 3.02/1.03  --bmc1_pre_inst_next_state              false
% 3.02/1.03  --bmc1_pre_inst_state                   false
% 3.02/1.03  --bmc1_pre_inst_reach_state             false
% 3.02/1.03  --bmc1_out_unsat_core                   false
% 3.02/1.03  --bmc1_aig_witness_out                  false
% 3.02/1.03  --bmc1_verbose                          false
% 3.02/1.03  --bmc1_dump_clauses_tptp                false
% 3.02/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.03  --bmc1_dump_file                        -
% 3.02/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.03  --bmc1_ucm_extend_mode                  1
% 3.02/1.03  --bmc1_ucm_init_mode                    2
% 3.02/1.03  --bmc1_ucm_cone_mode                    none
% 3.02/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.03  --bmc1_ucm_relax_model                  4
% 3.02/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.03  --bmc1_ucm_layered_model                none
% 3.02/1.03  --bmc1_ucm_max_lemma_size               10
% 3.02/1.03  
% 3.02/1.03  ------ AIG Options
% 3.02/1.03  
% 3.02/1.03  --aig_mode                              false
% 3.02/1.03  
% 3.02/1.03  ------ Instantiation Options
% 3.02/1.03  
% 3.02/1.03  --instantiation_flag                    true
% 3.02/1.03  --inst_sos_flag                         false
% 3.02/1.03  --inst_sos_phase                        true
% 3.02/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.03  --inst_lit_sel_side                     num_symb
% 3.02/1.03  --inst_solver_per_active                1400
% 3.02/1.03  --inst_solver_calls_frac                1.
% 3.02/1.03  --inst_passive_queue_type               priority_queues
% 3.02/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.03  --inst_passive_queues_freq              [25;2]
% 3.02/1.03  --inst_dismatching                      true
% 3.02/1.03  --inst_eager_unprocessed_to_passive     true
% 3.02/1.03  --inst_prop_sim_given                   true
% 3.02/1.03  --inst_prop_sim_new                     false
% 3.02/1.03  --inst_subs_new                         false
% 3.02/1.03  --inst_eq_res_simp                      false
% 3.02/1.03  --inst_subs_given                       false
% 3.02/1.03  --inst_orphan_elimination               true
% 3.02/1.03  --inst_learning_loop_flag               true
% 3.02/1.03  --inst_learning_start                   3000
% 3.02/1.03  --inst_learning_factor                  2
% 3.02/1.03  --inst_start_prop_sim_after_learn       3
% 3.02/1.03  --inst_sel_renew                        solver
% 3.02/1.03  --inst_lit_activity_flag                true
% 3.02/1.03  --inst_restr_to_given                   false
% 3.02/1.03  --inst_activity_threshold               500
% 3.02/1.03  --inst_out_proof                        true
% 3.02/1.03  
% 3.02/1.03  ------ Resolution Options
% 3.02/1.03  
% 3.02/1.03  --resolution_flag                       true
% 3.02/1.03  --res_lit_sel                           adaptive
% 3.02/1.03  --res_lit_sel_side                      none
% 3.02/1.03  --res_ordering                          kbo
% 3.02/1.03  --res_to_prop_solver                    active
% 3.02/1.03  --res_prop_simpl_new                    false
% 3.02/1.03  --res_prop_simpl_given                  true
% 3.02/1.03  --res_passive_queue_type                priority_queues
% 3.02/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.03  --res_passive_queues_freq               [15;5]
% 3.02/1.03  --res_forward_subs                      full
% 3.02/1.03  --res_backward_subs                     full
% 3.02/1.03  --res_forward_subs_resolution           true
% 3.02/1.03  --res_backward_subs_resolution          true
% 3.02/1.03  --res_orphan_elimination                true
% 3.02/1.03  --res_time_limit                        2.
% 3.02/1.03  --res_out_proof                         true
% 3.02/1.03  
% 3.02/1.03  ------ Superposition Options
% 3.02/1.03  
% 3.02/1.03  --superposition_flag                    true
% 3.02/1.03  --sup_passive_queue_type                priority_queues
% 3.02/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.03  --demod_completeness_check              fast
% 3.02/1.03  --demod_use_ground                      true
% 3.02/1.03  --sup_to_prop_solver                    passive
% 3.02/1.03  --sup_prop_simpl_new                    true
% 3.02/1.03  --sup_prop_simpl_given                  true
% 3.02/1.03  --sup_fun_splitting                     false
% 3.02/1.03  --sup_smt_interval                      50000
% 3.02/1.03  
% 3.02/1.03  ------ Superposition Simplification Setup
% 3.02/1.03  
% 3.02/1.03  --sup_indices_passive                   []
% 3.02/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.03  --sup_full_bw                           [BwDemod]
% 3.02/1.03  --sup_immed_triv                        [TrivRules]
% 3.02/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.03  --sup_immed_bw_main                     []
% 3.02/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.03  
% 3.02/1.03  ------ Combination Options
% 3.02/1.03  
% 3.02/1.03  --comb_res_mult                         3
% 3.02/1.03  --comb_sup_mult                         2
% 3.02/1.03  --comb_inst_mult                        10
% 3.02/1.03  
% 3.02/1.03  ------ Debug Options
% 3.02/1.03  
% 3.02/1.03  --dbg_backtrace                         false
% 3.02/1.03  --dbg_dump_prop_clauses                 false
% 3.02/1.03  --dbg_dump_prop_clauses_file            -
% 3.02/1.03  --dbg_out_stat                          false
% 3.02/1.03  ------ Parsing...
% 3.02/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/1.03  
% 3.02/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.02/1.03  
% 3.02/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/1.03  
% 3.02/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/1.03  ------ Proving...
% 3.02/1.03  ------ Problem Properties 
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  clauses                                 27
% 3.02/1.03  conjectures                             2
% 3.02/1.03  EPR                                     0
% 3.02/1.03  Horn                                    22
% 3.02/1.03  unary                                   4
% 3.02/1.03  binary                                  5
% 3.02/1.03  lits                                    75
% 3.02/1.03  lits eq                                 29
% 3.02/1.03  fd_pure                                 0
% 3.02/1.03  fd_pseudo                               0
% 3.02/1.03  fd_cond                                 4
% 3.02/1.03  fd_pseudo_cond                          1
% 3.02/1.03  AC symbols                              0
% 3.02/1.03  
% 3.02/1.03  ------ Schedule dynamic 5 is on 
% 3.02/1.03  
% 3.02/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  ------ 
% 3.02/1.03  Current options:
% 3.02/1.03  ------ 
% 3.02/1.03  
% 3.02/1.03  ------ Input Options
% 3.02/1.03  
% 3.02/1.03  --out_options                           all
% 3.02/1.03  --tptp_safe_out                         true
% 3.02/1.03  --problem_path                          ""
% 3.02/1.03  --include_path                          ""
% 3.02/1.03  --clausifier                            res/vclausify_rel
% 3.02/1.03  --clausifier_options                    --mode clausify
% 3.02/1.03  --stdin                                 false
% 3.02/1.03  --stats_out                             all
% 3.02/1.03  
% 3.02/1.03  ------ General Options
% 3.02/1.03  
% 3.02/1.03  --fof                                   false
% 3.02/1.03  --time_out_real                         305.
% 3.02/1.03  --time_out_virtual                      -1.
% 3.02/1.03  --symbol_type_check                     false
% 3.02/1.03  --clausify_out                          false
% 3.02/1.03  --sig_cnt_out                           false
% 3.02/1.03  --trig_cnt_out                          false
% 3.02/1.03  --trig_cnt_out_tolerance                1.
% 3.02/1.03  --trig_cnt_out_sk_spl                   false
% 3.02/1.03  --abstr_cl_out                          false
% 3.02/1.03  
% 3.02/1.03  ------ Global Options
% 3.02/1.03  
% 3.02/1.03  --schedule                              default
% 3.02/1.03  --add_important_lit                     false
% 3.02/1.03  --prop_solver_per_cl                    1000
% 3.02/1.03  --min_unsat_core                        false
% 3.02/1.03  --soft_assumptions                      false
% 3.02/1.03  --soft_lemma_size                       3
% 3.02/1.03  --prop_impl_unit_size                   0
% 3.02/1.03  --prop_impl_unit                        []
% 3.02/1.03  --share_sel_clauses                     true
% 3.02/1.03  --reset_solvers                         false
% 3.02/1.03  --bc_imp_inh                            [conj_cone]
% 3.02/1.03  --conj_cone_tolerance                   3.
% 3.02/1.03  --extra_neg_conj                        none
% 3.02/1.03  --large_theory_mode                     true
% 3.02/1.03  --prolific_symb_bound                   200
% 3.02/1.03  --lt_threshold                          2000
% 3.02/1.03  --clause_weak_htbl                      true
% 3.02/1.03  --gc_record_bc_elim                     false
% 3.02/1.03  
% 3.02/1.03  ------ Preprocessing Options
% 3.02/1.03  
% 3.02/1.03  --preprocessing_flag                    true
% 3.02/1.03  --time_out_prep_mult                    0.1
% 3.02/1.03  --splitting_mode                        input
% 3.02/1.03  --splitting_grd                         true
% 3.02/1.03  --splitting_cvd                         false
% 3.02/1.03  --splitting_cvd_svl                     false
% 3.02/1.03  --splitting_nvd                         32
% 3.02/1.03  --sub_typing                            true
% 3.02/1.03  --prep_gs_sim                           true
% 3.02/1.03  --prep_unflatten                        true
% 3.02/1.03  --prep_res_sim                          true
% 3.02/1.03  --prep_upred                            true
% 3.02/1.03  --prep_sem_filter                       exhaustive
% 3.02/1.03  --prep_sem_filter_out                   false
% 3.02/1.03  --pred_elim                             true
% 3.02/1.03  --res_sim_input                         true
% 3.02/1.03  --eq_ax_congr_red                       true
% 3.02/1.03  --pure_diseq_elim                       true
% 3.02/1.03  --brand_transform                       false
% 3.02/1.03  --non_eq_to_eq                          false
% 3.02/1.03  --prep_def_merge                        true
% 3.02/1.03  --prep_def_merge_prop_impl              false
% 3.02/1.03  --prep_def_merge_mbd                    true
% 3.02/1.03  --prep_def_merge_tr_red                 false
% 3.02/1.03  --prep_def_merge_tr_cl                  false
% 3.02/1.03  --smt_preprocessing                     true
% 3.02/1.03  --smt_ac_axioms                         fast
% 3.02/1.03  --preprocessed_out                      false
% 3.02/1.03  --preprocessed_stats                    false
% 3.02/1.03  
% 3.02/1.03  ------ Abstraction refinement Options
% 3.02/1.03  
% 3.02/1.03  --abstr_ref                             []
% 3.02/1.03  --abstr_ref_prep                        false
% 3.02/1.03  --abstr_ref_until_sat                   false
% 3.02/1.03  --abstr_ref_sig_restrict                funpre
% 3.02/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.03  --abstr_ref_under                       []
% 3.02/1.03  
% 3.02/1.03  ------ SAT Options
% 3.02/1.03  
% 3.02/1.03  --sat_mode                              false
% 3.02/1.03  --sat_fm_restart_options                ""
% 3.02/1.03  --sat_gr_def                            false
% 3.02/1.03  --sat_epr_types                         true
% 3.02/1.03  --sat_non_cyclic_types                  false
% 3.02/1.03  --sat_finite_models                     false
% 3.02/1.03  --sat_fm_lemmas                         false
% 3.02/1.03  --sat_fm_prep                           false
% 3.02/1.03  --sat_fm_uc_incr                        true
% 3.02/1.03  --sat_out_model                         small
% 3.02/1.03  --sat_out_clauses                       false
% 3.02/1.03  
% 3.02/1.03  ------ QBF Options
% 3.02/1.03  
% 3.02/1.03  --qbf_mode                              false
% 3.02/1.03  --qbf_elim_univ                         false
% 3.02/1.03  --qbf_dom_inst                          none
% 3.02/1.03  --qbf_dom_pre_inst                      false
% 3.02/1.03  --qbf_sk_in                             false
% 3.02/1.03  --qbf_pred_elim                         true
% 3.02/1.03  --qbf_split                             512
% 3.02/1.03  
% 3.02/1.03  ------ BMC1 Options
% 3.02/1.03  
% 3.02/1.03  --bmc1_incremental                      false
% 3.02/1.03  --bmc1_axioms                           reachable_all
% 3.02/1.03  --bmc1_min_bound                        0
% 3.02/1.03  --bmc1_max_bound                        -1
% 3.02/1.03  --bmc1_max_bound_default                -1
% 3.02/1.03  --bmc1_symbol_reachability              true
% 3.02/1.03  --bmc1_property_lemmas                  false
% 3.02/1.03  --bmc1_k_induction                      false
% 3.02/1.03  --bmc1_non_equiv_states                 false
% 3.02/1.03  --bmc1_deadlock                         false
% 3.02/1.03  --bmc1_ucm                              false
% 3.02/1.03  --bmc1_add_unsat_core                   none
% 3.02/1.03  --bmc1_unsat_core_children              false
% 3.02/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.03  --bmc1_out_stat                         full
% 3.02/1.03  --bmc1_ground_init                      false
% 3.02/1.03  --bmc1_pre_inst_next_state              false
% 3.02/1.03  --bmc1_pre_inst_state                   false
% 3.02/1.03  --bmc1_pre_inst_reach_state             false
% 3.02/1.03  --bmc1_out_unsat_core                   false
% 3.02/1.03  --bmc1_aig_witness_out                  false
% 3.02/1.03  --bmc1_verbose                          false
% 3.02/1.03  --bmc1_dump_clauses_tptp                false
% 3.02/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.03  --bmc1_dump_file                        -
% 3.02/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.03  --bmc1_ucm_extend_mode                  1
% 3.02/1.03  --bmc1_ucm_init_mode                    2
% 3.02/1.03  --bmc1_ucm_cone_mode                    none
% 3.02/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.03  --bmc1_ucm_relax_model                  4
% 3.02/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.03  --bmc1_ucm_layered_model                none
% 3.02/1.03  --bmc1_ucm_max_lemma_size               10
% 3.02/1.03  
% 3.02/1.03  ------ AIG Options
% 3.02/1.03  
% 3.02/1.03  --aig_mode                              false
% 3.02/1.03  
% 3.02/1.03  ------ Instantiation Options
% 3.02/1.03  
% 3.02/1.03  --instantiation_flag                    true
% 3.02/1.03  --inst_sos_flag                         false
% 3.02/1.03  --inst_sos_phase                        true
% 3.02/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.03  --inst_lit_sel_side                     none
% 3.02/1.03  --inst_solver_per_active                1400
% 3.02/1.03  --inst_solver_calls_frac                1.
% 3.02/1.03  --inst_passive_queue_type               priority_queues
% 3.02/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.03  --inst_passive_queues_freq              [25;2]
% 3.02/1.03  --inst_dismatching                      true
% 3.02/1.03  --inst_eager_unprocessed_to_passive     true
% 3.02/1.03  --inst_prop_sim_given                   true
% 3.02/1.03  --inst_prop_sim_new                     false
% 3.02/1.03  --inst_subs_new                         false
% 3.02/1.03  --inst_eq_res_simp                      false
% 3.02/1.03  --inst_subs_given                       false
% 3.02/1.03  --inst_orphan_elimination               true
% 3.02/1.03  --inst_learning_loop_flag               true
% 3.02/1.03  --inst_learning_start                   3000
% 3.02/1.03  --inst_learning_factor                  2
% 3.02/1.03  --inst_start_prop_sim_after_learn       3
% 3.02/1.03  --inst_sel_renew                        solver
% 3.02/1.03  --inst_lit_activity_flag                true
% 3.02/1.03  --inst_restr_to_given                   false
% 3.02/1.03  --inst_activity_threshold               500
% 3.02/1.03  --inst_out_proof                        true
% 3.02/1.03  
% 3.02/1.03  ------ Resolution Options
% 3.02/1.03  
% 3.02/1.03  --resolution_flag                       false
% 3.02/1.03  --res_lit_sel                           adaptive
% 3.02/1.03  --res_lit_sel_side                      none
% 3.02/1.03  --res_ordering                          kbo
% 3.02/1.03  --res_to_prop_solver                    active
% 3.02/1.03  --res_prop_simpl_new                    false
% 3.02/1.03  --res_prop_simpl_given                  true
% 3.02/1.03  --res_passive_queue_type                priority_queues
% 3.02/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.03  --res_passive_queues_freq               [15;5]
% 3.02/1.03  --res_forward_subs                      full
% 3.02/1.03  --res_backward_subs                     full
% 3.02/1.03  --res_forward_subs_resolution           true
% 3.02/1.03  --res_backward_subs_resolution          true
% 3.02/1.03  --res_orphan_elimination                true
% 3.02/1.03  --res_time_limit                        2.
% 3.02/1.03  --res_out_proof                         true
% 3.02/1.03  
% 3.02/1.03  ------ Superposition Options
% 3.02/1.03  
% 3.02/1.03  --superposition_flag                    true
% 3.02/1.03  --sup_passive_queue_type                priority_queues
% 3.02/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.03  --demod_completeness_check              fast
% 3.02/1.03  --demod_use_ground                      true
% 3.02/1.03  --sup_to_prop_solver                    passive
% 3.02/1.03  --sup_prop_simpl_new                    true
% 3.02/1.03  --sup_prop_simpl_given                  true
% 3.02/1.03  --sup_fun_splitting                     false
% 3.02/1.03  --sup_smt_interval                      50000
% 3.02/1.03  
% 3.02/1.03  ------ Superposition Simplification Setup
% 3.02/1.03  
% 3.02/1.03  --sup_indices_passive                   []
% 3.02/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.03  --sup_full_bw                           [BwDemod]
% 3.02/1.03  --sup_immed_triv                        [TrivRules]
% 3.02/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.03  --sup_immed_bw_main                     []
% 3.02/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.03  
% 3.02/1.03  ------ Combination Options
% 3.02/1.03  
% 3.02/1.03  --comb_res_mult                         3
% 3.02/1.03  --comb_sup_mult                         2
% 3.02/1.03  --comb_inst_mult                        10
% 3.02/1.03  
% 3.02/1.03  ------ Debug Options
% 3.02/1.03  
% 3.02/1.03  --dbg_backtrace                         false
% 3.02/1.03  --dbg_dump_prop_clauses                 false
% 3.02/1.03  --dbg_dump_prop_clauses_file            -
% 3.02/1.03  --dbg_out_stat                          false
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  ------ Proving...
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  % SZS status Theorem for theBenchmark.p
% 3.02/1.03  
% 3.02/1.03   Resolution empty clause
% 3.02/1.03  
% 3.02/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/1.03  
% 3.02/1.03  fof(f5,axiom,(
% 3.02/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f19,plain,(
% 3.02/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.02/1.03    inference(ennf_transformation,[],[f5])).
% 3.02/1.03  
% 3.02/1.03  fof(f36,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.02/1.03    inference(nnf_transformation,[],[f19])).
% 3.02/1.03  
% 3.02/1.03  fof(f37,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.02/1.03    inference(rectify,[],[f36])).
% 3.02/1.03  
% 3.02/1.03  fof(f38,plain,(
% 3.02/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.02/1.03    introduced(choice_axiom,[])).
% 3.02/1.03  
% 3.02/1.03  fof(f39,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.02/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.02/1.03  
% 3.02/1.03  fof(f59,plain,(
% 3.02/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f39])).
% 3.02/1.03  
% 3.02/1.03  fof(f12,axiom,(
% 3.02/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f28,plain,(
% 3.02/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.03    inference(ennf_transformation,[],[f12])).
% 3.02/1.03  
% 3.02/1.03  fof(f76,plain,(
% 3.02/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.03    inference(cnf_transformation,[],[f28])).
% 3.02/1.03  
% 3.02/1.03  fof(f14,conjecture,(
% 3.02/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f15,negated_conjecture,(
% 3.02/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.02/1.03    inference(negated_conjecture,[],[f14])).
% 3.02/1.03  
% 3.02/1.03  fof(f31,plain,(
% 3.02/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.02/1.03    inference(ennf_transformation,[],[f15])).
% 3.02/1.03  
% 3.02/1.03  fof(f32,plain,(
% 3.02/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.02/1.03    inference(flattening,[],[f31])).
% 3.02/1.03  
% 3.02/1.03  fof(f50,plain,(
% 3.02/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.02/1.03    introduced(choice_axiom,[])).
% 3.02/1.03  
% 3.02/1.03  fof(f49,plain,(
% 3.02/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.02/1.03    introduced(choice_axiom,[])).
% 3.02/1.03  
% 3.02/1.03  fof(f51,plain,(
% 3.02/1.03    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.02/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f32,f50,f49])).
% 3.02/1.03  
% 3.02/1.03  fof(f85,plain,(
% 3.02/1.03    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.02/1.03    inference(cnf_transformation,[],[f51])).
% 3.02/1.03  
% 3.02/1.03  fof(f86,plain,(
% 3.02/1.03    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.02/1.03    inference(cnf_transformation,[],[f51])).
% 3.02/1.03  
% 3.02/1.03  fof(f60,plain,(
% 3.02/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f39])).
% 3.02/1.03  
% 3.02/1.03  fof(f7,axiom,(
% 3.02/1.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f22,plain,(
% 3.02/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.02/1.03    inference(ennf_transformation,[],[f7])).
% 3.02/1.03  
% 3.02/1.03  fof(f23,plain,(
% 3.02/1.03    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.02/1.03    inference(flattening,[],[f22])).
% 3.02/1.03  
% 3.02/1.03  fof(f46,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.02/1.03    inference(nnf_transformation,[],[f23])).
% 3.02/1.03  
% 3.02/1.03  fof(f47,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.02/1.03    inference(flattening,[],[f46])).
% 3.02/1.03  
% 3.02/1.03  fof(f70,plain,(
% 3.02/1.03    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f47])).
% 3.02/1.03  
% 3.02/1.03  fof(f83,plain,(
% 3.02/1.03    v1_funct_1(sK7)),
% 3.02/1.03    inference(cnf_transformation,[],[f51])).
% 3.02/1.03  
% 3.02/1.03  fof(f9,axiom,(
% 3.02/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f25,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.03    inference(ennf_transformation,[],[f9])).
% 3.02/1.03  
% 3.02/1.03  fof(f73,plain,(
% 3.02/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.03    inference(cnf_transformation,[],[f25])).
% 3.02/1.03  
% 3.02/1.03  fof(f6,axiom,(
% 3.02/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f20,plain,(
% 3.02/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/1.03    inference(ennf_transformation,[],[f6])).
% 3.02/1.03  
% 3.02/1.03  fof(f21,plain,(
% 3.02/1.03    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.03    inference(flattening,[],[f20])).
% 3.02/1.03  
% 3.02/1.03  fof(f40,plain,(
% 3.02/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.03    inference(nnf_transformation,[],[f21])).
% 3.02/1.03  
% 3.02/1.03  fof(f41,plain,(
% 3.02/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.03    inference(rectify,[],[f40])).
% 3.02/1.03  
% 3.02/1.03  fof(f44,plain,(
% 3.02/1.03    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.02/1.03    introduced(choice_axiom,[])).
% 3.02/1.03  
% 3.02/1.03  fof(f43,plain,(
% 3.02/1.03    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.02/1.03    introduced(choice_axiom,[])).
% 3.02/1.03  
% 3.02/1.03  fof(f42,plain,(
% 3.02/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.02/1.03    introduced(choice_axiom,[])).
% 3.02/1.03  
% 3.02/1.03  fof(f45,plain,(
% 3.02/1.03    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).
% 3.02/1.03  
% 3.02/1.03  fof(f65,plain,(
% 3.02/1.03    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f45])).
% 3.02/1.03  
% 3.02/1.03  fof(f90,plain,(
% 3.02/1.03    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.03    inference(equality_resolution,[],[f65])).
% 3.02/1.03  
% 3.02/1.03  fof(f91,plain,(
% 3.02/1.03    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.03    inference(equality_resolution,[],[f90])).
% 3.02/1.03  
% 3.02/1.03  fof(f84,plain,(
% 3.02/1.03    v1_funct_2(sK7,sK4,sK5)),
% 3.02/1.03    inference(cnf_transformation,[],[f51])).
% 3.02/1.03  
% 3.02/1.03  fof(f13,axiom,(
% 3.02/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f29,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.03    inference(ennf_transformation,[],[f13])).
% 3.02/1.03  
% 3.02/1.03  fof(f30,plain,(
% 3.02/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.03    inference(flattening,[],[f29])).
% 3.02/1.03  
% 3.02/1.03  fof(f48,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.03    inference(nnf_transformation,[],[f30])).
% 3.02/1.03  
% 3.02/1.03  fof(f77,plain,(
% 3.02/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.03    inference(cnf_transformation,[],[f48])).
% 3.02/1.03  
% 3.02/1.03  fof(f11,axiom,(
% 3.02/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f27,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.03    inference(ennf_transformation,[],[f11])).
% 3.02/1.03  
% 3.02/1.03  fof(f75,plain,(
% 3.02/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.03    inference(cnf_transformation,[],[f27])).
% 3.02/1.03  
% 3.02/1.03  fof(f66,plain,(
% 3.02/1.03    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f45])).
% 3.02/1.03  
% 3.02/1.03  fof(f61,plain,(
% 3.02/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f39])).
% 3.02/1.03  
% 3.02/1.03  fof(f87,plain,(
% 3.02/1.03    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f51])).
% 3.02/1.03  
% 3.02/1.03  fof(f1,axiom,(
% 3.02/1.03    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f33,plain,(
% 3.02/1.03    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.02/1.03    inference(nnf_transformation,[],[f1])).
% 3.02/1.03  
% 3.02/1.03  fof(f34,plain,(
% 3.02/1.03    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.02/1.03    inference(flattening,[],[f33])).
% 3.02/1.03  
% 3.02/1.03  fof(f53,plain,(
% 3.02/1.03    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.02/1.03    inference(cnf_transformation,[],[f34])).
% 3.02/1.03  
% 3.02/1.03  fof(f89,plain,(
% 3.02/1.03    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.02/1.03    inference(equality_resolution,[],[f53])).
% 3.02/1.03  
% 3.02/1.03  fof(f10,axiom,(
% 3.02/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f16,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.02/1.03    inference(pure_predicate_removal,[],[f10])).
% 3.02/1.03  
% 3.02/1.03  fof(f26,plain,(
% 3.02/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.03    inference(ennf_transformation,[],[f16])).
% 3.02/1.03  
% 3.02/1.03  fof(f74,plain,(
% 3.02/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.03    inference(cnf_transformation,[],[f26])).
% 3.02/1.03  
% 3.02/1.03  fof(f3,axiom,(
% 3.02/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f18,plain,(
% 3.02/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.02/1.03    inference(ennf_transformation,[],[f3])).
% 3.02/1.03  
% 3.02/1.03  fof(f35,plain,(
% 3.02/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.02/1.03    inference(nnf_transformation,[],[f18])).
% 3.02/1.03  
% 3.02/1.03  fof(f56,plain,(
% 3.02/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f35])).
% 3.02/1.03  
% 3.02/1.03  fof(f8,axiom,(
% 3.02/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.02/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.03  
% 3.02/1.03  fof(f24,plain,(
% 3.02/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.02/1.03    inference(ennf_transformation,[],[f8])).
% 3.02/1.03  
% 3.02/1.03  fof(f72,plain,(
% 3.02/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.02/1.03    inference(cnf_transformation,[],[f24])).
% 3.02/1.03  
% 3.02/1.03  fof(f54,plain,(
% 3.02/1.03    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.02/1.03    inference(cnf_transformation,[],[f34])).
% 3.02/1.03  
% 3.02/1.03  fof(f88,plain,(
% 3.02/1.03    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.02/1.03    inference(equality_resolution,[],[f54])).
% 3.02/1.03  
% 3.02/1.03  cnf(c_10,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.02/1.03      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.02/1.03      | ~ v1_relat_1(X1) ),
% 3.02/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1339,plain,
% 3.02/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.02/1.03      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.02/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_24,plain,
% 3.02/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.02/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_33,negated_conjecture,
% 3.02/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.02/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_464,plain,
% 3.02/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | sK7 != X2 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_465,plain,
% 3.02/1.03      ( k7_relset_1(X0,X1,sK7,X2) = k9_relat_1(sK7,X2)
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_464]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1543,plain,
% 3.02/1.03      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.02/1.03      inference(equality_resolution,[status(thm)],[c_465]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_32,negated_conjecture,
% 3.02/1.03      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.02/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1337,plain,
% 3.02/1.03      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1573,plain,
% 3.02/1.03      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.02/1.03      inference(demodulation,[status(thm)],[c_1543,c_1337]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_9,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.02/1.03      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.02/1.03      | ~ v1_relat_1(X1) ),
% 3.02/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1340,plain,
% 3.02/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.02/1.03      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.02/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_18,plain,
% 3.02/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.02/1.03      | ~ v1_funct_1(X2)
% 3.02/1.03      | ~ v1_relat_1(X2)
% 3.02/1.03      | k1_funct_1(X2,X0) = X1 ),
% 3.02/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_35,negated_conjecture,
% 3.02/1.03      ( v1_funct_1(sK7) ),
% 3.02/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_745,plain,
% 3.02/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.02/1.03      | ~ v1_relat_1(X2)
% 3.02/1.03      | k1_funct_1(X2,X0) = X1
% 3.02/1.03      | sK7 != X2 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_746,plain,
% 3.02/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.02/1.03      | ~ v1_relat_1(sK7)
% 3.02/1.03      | k1_funct_1(sK7,X0) = X1 ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_745]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1325,plain,
% 3.02/1.03      ( k1_funct_1(sK7,X0) = X1
% 3.02/1.03      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_747,plain,
% 3.02/1.03      ( k1_funct_1(sK7,X0) = X1
% 3.02/1.03      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_997,plain,( X0 = X0 ),theory(equality) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1554,plain,
% 3.02/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.02/1.03      inference(instantiation,[status(thm)],[c_997]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_21,plain,
% 3.02/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.02/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_482,plain,
% 3.02/1.03      ( v1_relat_1(X0)
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | sK7 != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_483,plain,
% 3.02/1.03      ( v1_relat_1(sK7)
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_482]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1557,plain,
% 3.02/1.03      ( v1_relat_1(sK7)
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.02/1.03      inference(instantiation,[status(thm)],[c_483]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1558,plain,
% 3.02/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | v1_relat_1(sK7) = iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1951,plain,
% 3.02/1.03      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.02/1.03      | k1_funct_1(sK7,X0) = X1 ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1325,c_747,c_1554,c_1558]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1952,plain,
% 3.02/1.03      ( k1_funct_1(sK7,X0) = X1
% 3.02/1.03      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_1951]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2746,plain,
% 3.02/1.03      ( k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0
% 3.02/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_1340,c_1952]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2827,plain,
% 3.02/1.03      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.02/1.03      | k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0 ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_2746,c_1554,c_1558]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2828,plain,
% 3.02/1.03      ( k1_funct_1(sK7,sK0(X0,X1,sK7)) = X0
% 3.02/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_2827]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2839,plain,
% 3.02/1.03      ( k1_funct_1(sK7,sK0(sK8,sK6,sK7)) = sK8 ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_1573,c_2828]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_14,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.02/1.03      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.02/1.03      | ~ v1_funct_1(X1)
% 3.02/1.03      | ~ v1_relat_1(X1) ),
% 3.02/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_709,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.02/1.03      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.02/1.03      | ~ v1_relat_1(X1)
% 3.02/1.03      | sK7 != X1 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_35]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_710,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.02/1.03      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 3.02/1.03      | ~ v1_relat_1(sK7) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_709]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1327,plain,
% 3.02/1.03      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.02/1.03      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_711,plain,
% 3.02/1.03      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.02/1.03      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2499,plain,
% 3.02/1.03      ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.02/1.03      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1327,c_711,c_1554,c_1558]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2500,plain,
% 3.02/1.03      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.02/1.03      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_2499]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2878,plain,
% 3.02/1.03      ( r2_hidden(sK0(sK8,sK6,sK7),k1_relat_1(sK7)) != iProver_top
% 3.02/1.03      | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_2839,c_2500]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2941,plain,
% 3.02/1.03      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.02/1.03      | r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_1339,c_2878]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3430,plain,
% 3.02/1.03      ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_2941,c_1554,c_1558,c_1573]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_34,negated_conjecture,
% 3.02/1.03      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.02/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_30,plain,
% 3.02/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.02/1.03      | k1_xboole_0 = X2 ),
% 3.02/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_428,plain,
% 3.02/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | sK7 != X0
% 3.02/1.03      | k1_xboole_0 = X2 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_30,c_33]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_429,plain,
% 3.02/1.03      ( ~ v1_funct_2(sK7,X0,X1)
% 3.02/1.03      | k1_relset_1(X0,X1,sK7) = X0
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | k1_xboole_0 = X1 ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_428]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_808,plain,
% 3.02/1.03      ( k1_relset_1(X0,X1,sK7) = X0
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | sK5 != X1
% 3.02/1.03      | sK4 != X0
% 3.02/1.03      | sK7 != sK7
% 3.02/1.03      | k1_xboole_0 = X1 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_34,c_429]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_809,plain,
% 3.02/1.03      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | k1_xboole_0 = sK5 ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_808]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_881,plain,
% 3.02/1.03      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 3.02/1.03      inference(equality_resolution_simp,[status(thm)],[c_809]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_23,plain,
% 3.02/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_473,plain,
% 3.02/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | sK7 != X2 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_474,plain,
% 3.02/1.03      ( k1_relset_1(X0,X1,sK7) = k1_relat_1(sK7)
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_473]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1540,plain,
% 3.02/1.03      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.02/1.03      inference(equality_resolution,[status(thm)],[c_474]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1649,plain,
% 3.02/1.03      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.02/1.03      inference(demodulation,[status(thm)],[c_881,c_1540]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_13,plain,
% 3.02/1.03      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.02/1.03      | r2_hidden(sK1(X0,X1),X1)
% 3.02/1.03      | ~ v1_funct_1(X0)
% 3.02/1.03      | ~ v1_relat_1(X0)
% 3.02/1.03      | k2_relat_1(X0) = X1 ),
% 3.02/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_613,plain,
% 3.02/1.03      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 3.02/1.03      | r2_hidden(sK1(X0,X1),X1)
% 3.02/1.03      | ~ v1_relat_1(X0)
% 3.02/1.03      | k2_relat_1(X0) = X1
% 3.02/1.03      | sK7 != X0 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_35]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_614,plain,
% 3.02/1.03      ( r2_hidden(sK2(sK7,X0),k1_relat_1(sK7))
% 3.02/1.03      | r2_hidden(sK1(sK7,X0),X0)
% 3.02/1.03      | ~ v1_relat_1(sK7)
% 3.02/1.03      | k2_relat_1(sK7) = X0 ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_613]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1333,plain,
% 3.02/1.03      ( k2_relat_1(sK7) = X0
% 3.02/1.03      | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.02/1.03      | r2_hidden(sK1(sK7,X0),X0) = iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_615,plain,
% 3.02/1.03      ( k2_relat_1(sK7) = X0
% 3.02/1.03      | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.02/1.03      | r2_hidden(sK1(sK7,X0),X0) = iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2551,plain,
% 3.02/1.03      ( r2_hidden(sK1(sK7,X0),X0) = iProver_top
% 3.02/1.03      | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.02/1.03      | k2_relat_1(sK7) = X0 ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_1333,c_615,c_1554,c_1558]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2552,plain,
% 3.02/1.03      ( k2_relat_1(sK7) = X0
% 3.02/1.03      | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.02/1.03      | r2_hidden(sK1(sK7,X0),X0) = iProver_top ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_2551]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2560,plain,
% 3.02/1.03      ( k2_relat_1(sK7) = X0
% 3.02/1.03      | sK5 = k1_xboole_0
% 3.02/1.03      | r2_hidden(sK2(sK7,X0),sK4) = iProver_top
% 3.02/1.03      | r2_hidden(sK1(sK7,X0),X0) = iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_1649,c_2552]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_8,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.02/1.03      | r2_hidden(sK0(X0,X2,X1),X2)
% 3.02/1.03      | ~ v1_relat_1(X1) ),
% 3.02/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1341,plain,
% 3.02/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.02/1.03      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 3.02/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2660,plain,
% 3.02/1.03      ( sK5 = k1_xboole_0
% 3.02/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.02/1.03      | r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_1649,c_1339]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3441,plain,
% 3.02/1.03      ( r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top
% 3.02/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.02/1.03      | sK5 = k1_xboole_0 ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_2660,c_1554,c_1558]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3442,plain,
% 3.02/1.03      ( sK5 = k1_xboole_0
% 3.02/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.02/1.03      | r2_hidden(sK0(X0,X1,sK7),sK4) = iProver_top ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_3441]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_31,negated_conjecture,
% 3.02/1.03      ( ~ r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK6) | k1_funct_1(sK7,X0) != sK8 ),
% 3.02/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1338,plain,
% 3.02/1.03      ( k1_funct_1(sK7,X0) != sK8
% 3.02/1.03      | r2_hidden(X0,sK4) != iProver_top
% 3.02/1.03      | r2_hidden(X0,sK6) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_2879,plain,
% 3.02/1.03      ( r2_hidden(sK0(sK8,sK6,sK7),sK4) != iProver_top
% 3.02/1.03      | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_2839,c_1338]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3450,plain,
% 3.02/1.03      ( sK5 = k1_xboole_0
% 3.02/1.03      | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top
% 3.02/1.03      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_3442,c_2879]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3912,plain,
% 3.02/1.03      ( r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top | sK5 = k1_xboole_0 ),
% 3.02/1.03      inference(global_propositional_subsumption,[status(thm)],[c_3450,c_1573]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3913,plain,
% 3.02/1.03      ( sK5 = k1_xboole_0 | r2_hidden(sK0(sK8,sK6,sK7),sK6) != iProver_top ),
% 3.02/1.03      inference(renaming,[status(thm)],[c_3912]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3918,plain,
% 3.02/1.03      ( sK5 = k1_xboole_0
% 3.02/1.03      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.02/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_1341,c_3913]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3964,plain,
% 3.02/1.03      ( sK5 = k1_xboole_0 ),
% 3.02/1.03      inference(global_propositional_subsumption,
% 3.02/1.03                [status(thm)],
% 3.02/1.03                [c_2560,c_1554,c_1558,c_1573,c_3918]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1,plain,
% 3.02/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.02/1.03      inference(cnf_transformation,[],[f89]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_22,plain,
% 3.02/1.03      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.02/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_5,plain,
% 3.02/1.03      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 3.02/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_378,plain,
% 3.02/1.03      ( r1_tarski(k2_relat_1(X0),X1)
% 3.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.02/1.03      | ~ v1_relat_1(X0) ),
% 3.02/1.03      inference(resolution,[status(thm)],[c_22,c_5]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_388,plain,
% 3.02/1.03      ( r1_tarski(k2_relat_1(X0),X1)
% 3.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.02/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_378,c_21]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_20,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.02/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_398,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,X1)
% 3.02/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.02/1.03      | X0 != X4
% 3.02/1.03      | k2_relat_1(X2) != X1 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_388,c_20]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_399,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.02/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_398]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_559,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | sK7 != X1 ),
% 3.02/1.03      inference(resolution_lifted,[status(thm)],[c_33,c_399]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_560,plain,
% 3.02/1.03      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 3.02/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.02/1.03      inference(unflattening,[status(thm)],[c_559]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1334,plain,
% 3.02/1.03      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 3.02/1.03      | r2_hidden(X1,k2_relat_1(sK7)) != iProver_top ),
% 3.02/1.03      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_1878,plain,
% 3.02/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k1_xboole_0)
% 3.02/1.03      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_1,c_1334]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_3969,plain,
% 3.02/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 3.02/1.03      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.02/1.03      inference(demodulation,[status(thm)],[c_3964,c_1878]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_0,plain,
% 3.02/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.02/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4029,plain,
% 3.02/1.03      ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 3.02/1.03      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.02/1.03      inference(demodulation,[status(thm)],[c_3969,c_0]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4030,plain,
% 3.02/1.03      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.02/1.03      inference(equality_resolution_simp,[status(thm)],[c_4029]) ).
% 3.02/1.03  
% 3.02/1.03  cnf(c_4607,plain,
% 3.02/1.03      ( $false ),
% 3.02/1.03      inference(superposition,[status(thm)],[c_3430,c_4030]) ).
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/1.03  
% 3.02/1.03  ------                               Statistics
% 3.02/1.03  
% 3.02/1.03  ------ General
% 3.02/1.03  
% 3.02/1.03  abstr_ref_over_cycles:                  0
% 3.02/1.03  abstr_ref_under_cycles:                 0
% 3.02/1.03  gc_basic_clause_elim:                   0
% 3.02/1.03  forced_gc_time:                         0
% 3.02/1.03  parsing_time:                           0.01
% 3.02/1.03  unif_index_cands_time:                  0.
% 3.02/1.03  unif_index_add_time:                    0.
% 3.02/1.03  orderings_time:                         0.
% 3.02/1.03  out_proof_time:                         0.016
% 3.02/1.03  total_time:                             0.21
% 3.02/1.03  num_of_symbols:                         57
% 3.02/1.03  num_of_terms:                           4990
% 3.02/1.03  
% 3.02/1.03  ------ Preprocessing
% 3.02/1.03  
% 3.02/1.03  num_of_splits:                          0
% 3.02/1.03  num_of_split_atoms:                     0
% 3.02/1.03  num_of_reused_defs:                     0
% 3.02/1.03  num_eq_ax_congr_red:                    32
% 3.02/1.03  num_of_sem_filtered_clauses:            1
% 3.02/1.03  num_of_subtypes:                        0
% 3.02/1.03  monotx_restored_types:                  0
% 3.02/1.03  sat_num_of_epr_types:                   0
% 3.02/1.03  sat_num_of_non_cyclic_types:            0
% 3.02/1.03  sat_guarded_non_collapsed_types:        0
% 3.02/1.03  num_pure_diseq_elim:                    0
% 3.02/1.03  simp_replaced_by:                       0
% 3.02/1.03  res_preprocessed:                       150
% 3.02/1.03  prep_upred:                             0
% 3.02/1.03  prep_unflattend:                        38
% 3.02/1.03  smt_new_axioms:                         0
% 3.02/1.03  pred_elim_cands:                        2
% 3.02/1.03  pred_elim:                              5
% 3.02/1.03  pred_elim_cl:                           9
% 3.02/1.03  pred_elim_cycles:                       7
% 3.02/1.03  merged_defs:                            0
% 3.02/1.03  merged_defs_ncl:                        0
% 3.02/1.03  bin_hyper_res:                          0
% 3.02/1.03  prep_cycles:                            4
% 3.02/1.03  pred_elim_time:                         0.012
% 3.02/1.03  splitting_time:                         0.
% 3.02/1.03  sem_filter_time:                        0.
% 3.02/1.03  monotx_time:                            0.
% 3.02/1.03  subtype_inf_time:                       0.
% 3.02/1.03  
% 3.02/1.03  ------ Problem properties
% 3.02/1.03  
% 3.02/1.03  clauses:                                27
% 3.02/1.03  conjectures:                            2
% 3.02/1.03  epr:                                    0
% 3.02/1.03  horn:                                   22
% 3.02/1.03  ground:                                 4
% 3.02/1.03  unary:                                  4
% 3.02/1.03  binary:                                 5
% 3.02/1.03  lits:                                   75
% 3.02/1.03  lits_eq:                                29
% 3.02/1.03  fd_pure:                                0
% 3.02/1.03  fd_pseudo:                              0
% 3.02/1.03  fd_cond:                                4
% 3.02/1.03  fd_pseudo_cond:                         1
% 3.02/1.03  ac_symbols:                             0
% 3.02/1.03  
% 3.02/1.03  ------ Propositional Solver
% 3.02/1.03  
% 3.02/1.03  prop_solver_calls:                      27
% 3.02/1.03  prop_fast_solver_calls:                 1155
% 3.02/1.03  smt_solver_calls:                       0
% 3.02/1.03  smt_fast_solver_calls:                  0
% 3.02/1.03  prop_num_of_clauses:                    1550
% 3.02/1.03  prop_preprocess_simplified:             5335
% 3.02/1.03  prop_fo_subsumed:                       28
% 3.02/1.03  prop_solver_time:                       0.
% 3.02/1.03  smt_solver_time:                        0.
% 3.02/1.03  smt_fast_solver_time:                   0.
% 3.02/1.03  prop_fast_solver_time:                  0.
% 3.02/1.03  prop_unsat_core_time:                   0.
% 3.02/1.03  
% 3.02/1.03  ------ QBF
% 3.02/1.03  
% 3.02/1.03  qbf_q_res:                              0
% 3.02/1.03  qbf_num_tautologies:                    0
% 3.02/1.03  qbf_prep_cycles:                        0
% 3.02/1.03  
% 3.02/1.03  ------ BMC1
% 3.02/1.03  
% 3.02/1.03  bmc1_current_bound:                     -1
% 3.02/1.03  bmc1_last_solved_bound:                 -1
% 3.02/1.03  bmc1_unsat_core_size:                   -1
% 3.02/1.03  bmc1_unsat_core_parents_size:           -1
% 3.02/1.03  bmc1_merge_next_fun:                    0
% 3.02/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.02/1.03  
% 3.02/1.03  ------ Instantiation
% 3.02/1.03  
% 3.02/1.03  inst_num_of_clauses:                    419
% 3.02/1.03  inst_num_in_passive:                    90
% 3.02/1.03  inst_num_in_active:                     286
% 3.02/1.03  inst_num_in_unprocessed:                43
% 3.02/1.03  inst_num_of_loops:                      350
% 3.02/1.03  inst_num_of_learning_restarts:          0
% 3.02/1.03  inst_num_moves_active_passive:          60
% 3.02/1.03  inst_lit_activity:                      0
% 3.02/1.03  inst_lit_activity_moves:                0
% 3.02/1.03  inst_num_tautologies:                   0
% 3.02/1.03  inst_num_prop_implied:                  0
% 3.02/1.03  inst_num_existing_simplified:           0
% 3.02/1.03  inst_num_eq_res_simplified:             0
% 3.02/1.03  inst_num_child_elim:                    0
% 3.02/1.03  inst_num_of_dismatching_blockings:      126
% 3.02/1.03  inst_num_of_non_proper_insts:           301
% 3.02/1.03  inst_num_of_duplicates:                 0
% 3.02/1.03  inst_inst_num_from_inst_to_res:         0
% 3.02/1.03  inst_dismatching_checking_time:         0.
% 3.02/1.03  
% 3.02/1.03  ------ Resolution
% 3.02/1.03  
% 3.02/1.03  res_num_of_clauses:                     0
% 3.02/1.03  res_num_in_passive:                     0
% 3.02/1.03  res_num_in_active:                      0
% 3.02/1.03  res_num_of_loops:                       154
% 3.02/1.03  res_forward_subset_subsumed:            21
% 3.02/1.03  res_backward_subset_subsumed:           0
% 3.02/1.03  res_forward_subsumed:                   0
% 3.02/1.03  res_backward_subsumed:                  0
% 3.02/1.03  res_forward_subsumption_resolution:     1
% 3.02/1.03  res_backward_subsumption_resolution:    0
% 3.02/1.03  res_clause_to_clause_subsumption:       197
% 3.02/1.03  res_orphan_elimination:                 0
% 3.02/1.03  res_tautology_del:                      43
% 3.02/1.03  res_num_eq_res_simplified:              1
% 3.02/1.03  res_num_sel_changes:                    0
% 3.02/1.03  res_moves_from_active_to_pass:          0
% 3.02/1.03  
% 3.02/1.03  ------ Superposition
% 3.02/1.03  
% 3.02/1.03  sup_time_total:                         0.
% 3.02/1.03  sup_time_generating:                    0.
% 3.02/1.03  sup_time_sim_full:                      0.
% 3.02/1.03  sup_time_sim_immed:                     0.
% 3.02/1.03  
% 3.02/1.03  sup_num_of_clauses:                     102
% 3.02/1.03  sup_num_in_active:                      51
% 3.02/1.03  sup_num_in_passive:                     51
% 3.02/1.03  sup_num_of_loops:                       69
% 3.02/1.03  sup_fw_superposition:                   75
% 3.02/1.03  sup_bw_superposition:                   51
% 3.02/1.03  sup_immediate_simplified:               27
% 3.02/1.03  sup_given_eliminated:                   0
% 3.02/1.03  comparisons_done:                       0
% 3.02/1.03  comparisons_avoided:                    19
% 3.02/1.03  
% 3.02/1.03  ------ Simplifications
% 3.02/1.03  
% 3.02/1.03  
% 3.02/1.03  sim_fw_subset_subsumed:                 7
% 3.02/1.03  sim_bw_subset_subsumed:                 9
% 3.02/1.03  sim_fw_subsumed:                        3
% 3.02/1.03  sim_bw_subsumed:                        3
% 3.02/1.03  sim_fw_subsumption_res:                 0
% 3.02/1.03  sim_bw_subsumption_res:                 0
% 3.02/1.03  sim_tautology_del:                      3
% 3.02/1.03  sim_eq_tautology_del:                   10
% 3.02/1.03  sim_eq_res_simp:                        8
% 3.02/1.03  sim_fw_demodulated:                     14
% 3.02/1.03  sim_bw_demodulated:                     14
% 3.02/1.03  sim_light_normalised:                   3
% 3.02/1.03  sim_joinable_taut:                      0
% 3.02/1.03  sim_joinable_simp:                      0
% 3.02/1.03  sim_ac_normalised:                      0
% 3.02/1.03  sim_smt_subsumption:                    0
% 3.02/1.03  
%------------------------------------------------------------------------------
