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
% DateTime   : Thu Dec  3 12:10:10 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 357 expanded)
%              Number of clauses        :   75 ( 131 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  458 (1590 expanded)
%              Number of equality atoms :  196 ( 443 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK7,X4) != sK4
          | ~ m1_subset_1(X4,sK5) )
      & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ! [X4] :
        ( k1_funct_1(sK7,X4) != sK4
        | ~ m1_subset_1(X4,sK5) )
    & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f36])).

fof(f60,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f59,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) != X3
              | ~ r2_hidden(X4,X0) )
          & r2_hidden(X3,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) != X3
              | ~ r2_hidden(X4,X0) )
          & r2_hidden(X3,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) != X3
              | ~ r2_hidden(X4,X0) )
          & r2_hidden(X3,X1) )
     => ( ! [X4] :
            ( k1_funct_1(X2,X4) != sK3(X0,X1,X2)
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(sK3(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ( ! [X4] :
            ( k1_funct_1(X2,X4) != sK3(X0,X1,X2)
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(sK3(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) != sK4
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1048,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X2
    | sK5 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_1049,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_1048])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1051,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_23])).

cnf(c_1756,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1760,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2298,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1756,c_1760])).

cnf(c_2362,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1051,c_2298])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_304,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_305,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_1754,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1763,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2153,plain,
    ( m1_subset_1(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1754,c_1763])).

cnf(c_28,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1967,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2066,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_2067,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2066])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2092,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2093,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2092])).

cnf(c_3075,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | m1_subset_1(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2153,c_28,c_2067,c_2093])).

cnf(c_3076,plain,
    ( m1_subset_1(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3075])).

cnf(c_3083,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK2(sK7,X0),sK5) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2362,c_3076])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_370,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | k2_relset_1(X1,X2,X0) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_371,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK3(X0,X1,sK7),X1)
    | k2_relset_1(X0,X1,sK7) = X1 ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_1121,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK3(X0,X1,sK7),X1)
    | k2_relset_1(X0,X1,sK7) = X1
    | sK6 != X1
    | sK5 != X0
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_371])).

cnf(c_1122,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(sK3(sK5,sK6,sK7),sK6)
    | k2_relset_1(sK5,sK6,sK7) = sK6 ),
    inference(unflattening,[status(thm)],[c_1121])).

cnf(c_1338,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1369,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_1339,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2321,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_2322,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2321])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1759,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2185,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1756,c_1759])).

cnf(c_1757,plain,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2301,plain,
    ( r2_hidden(sK4,k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2185,c_1757])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK2(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_1753,plain,
    ( k1_funct_1(sK7,sK2(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_2352,plain,
    ( k1_funct_1(sK7,sK2(sK7,sK4)) = sK4
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_1753])).

cnf(c_2122,plain,
    ( X0 != X1
    | X0 = k2_relset_1(sK5,sK6,sK7)
    | k2_relset_1(sK5,sK6,sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_2397,plain,
    ( X0 = k2_relset_1(sK5,sK6,sK7)
    | X0 != sK6
    | k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_2398,plain,
    ( k2_relset_1(sK5,sK6,sK7) != sK6
    | k1_xboole_0 = k2_relset_1(sK5,sK6,sK7)
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_1340,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1993,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    | X1 != k2_relset_1(sK5,sK6,sK7)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_2712,plain,
    ( r2_hidden(k1_funct_1(sK7,sK2(sK7,sK4)),X0)
    | ~ r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    | X0 != k2_relset_1(sK5,sK6,sK7)
    | k1_funct_1(sK7,sK2(sK7,sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_1993])).

cnf(c_2714,plain,
    ( r2_hidden(k1_funct_1(sK7,sK2(sK7,sK4)),k1_xboole_0)
    | ~ r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    | k1_funct_1(sK7,sK2(sK7,sK4)) != sK4
    | k1_xboole_0 != k2_relset_1(sK5,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_2712])).

cnf(c_2606,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3(sK5,sK6,sK7),sK6)
    | X0 != sK3(sK5,sK6,sK7)
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_2906,plain,
    ( r2_hidden(sK3(sK5,sK6,sK7),X0)
    | ~ r2_hidden(sK3(sK5,sK6,sK7),sK6)
    | X0 != sK6
    | sK3(sK5,sK6,sK7) != sK3(sK5,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_2606])).

cnf(c_2909,plain,
    ( ~ r2_hidden(sK3(sK5,sK6,sK7),sK6)
    | r2_hidden(sK3(sK5,sK6,sK7),k1_xboole_0)
    | sK3(sK5,sK6,sK7) != sK3(sK5,sK6,sK7)
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2906])).

cnf(c_2907,plain,
    ( sK3(sK5,sK6,sK7) = sK3(sK5,sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_293,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_294,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_3936,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK2(sK7,sK4)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_7731,plain,
    ( ~ r2_hidden(sK3(sK5,sK6,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_11319,plain,
    ( m1_subset_1(sK2(sK7,X0),sK5) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3083,c_23,c_28,c_22,c_1122,c_1369,c_2067,c_2093,c_2322,c_2352,c_2398,c_2714,c_2909,c_2907,c_3936,c_7731])).

cnf(c_3007,plain,
    ( k1_funct_1(sK7,sK2(sK7,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2352,c_28,c_2067,c_2093])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | k1_funct_1(sK7,X0) != sK4 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1758,plain,
    ( k1_funct_1(sK7,X0) != sK4
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3012,plain,
    ( m1_subset_1(sK2(sK7,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3007,c_1758])).

cnf(c_11327,plain,
    ( r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11319,c_3012])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11327,c_2301])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 15:21:57 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 3.14/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/0.96  
% 3.14/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.96  
% 3.14/0.96  ------  iProver source info
% 3.14/0.96  
% 3.14/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.96  git: non_committed_changes: false
% 3.14/0.96  git: last_make_outside_of_git: false
% 3.14/0.96  
% 3.14/0.96  ------ 
% 3.14/0.96  
% 3.14/0.96  ------ Input Options
% 3.14/0.96  
% 3.14/0.96  --out_options                           all
% 3.14/0.96  --tptp_safe_out                         true
% 3.14/0.96  --problem_path                          ""
% 3.14/0.96  --include_path                          ""
% 3.14/0.96  --clausifier                            res/vclausify_rel
% 3.14/0.96  --clausifier_options                    --mode clausify
% 3.14/0.96  --stdin                                 false
% 3.14/0.96  --stats_out                             all
% 3.14/0.96  
% 3.14/0.96  ------ General Options
% 3.14/0.96  
% 3.14/0.96  --fof                                   false
% 3.14/0.96  --time_out_real                         305.
% 3.14/0.96  --time_out_virtual                      -1.
% 3.14/0.96  --symbol_type_check                     false
% 3.14/0.96  --clausify_out                          false
% 3.14/0.96  --sig_cnt_out                           false
% 3.14/0.96  --trig_cnt_out                          false
% 3.14/0.96  --trig_cnt_out_tolerance                1.
% 3.14/0.96  --trig_cnt_out_sk_spl                   false
% 3.14/0.96  --abstr_cl_out                          false
% 3.14/0.96  
% 3.14/0.96  ------ Global Options
% 3.14/0.96  
% 3.14/0.96  --schedule                              default
% 3.14/0.96  --add_important_lit                     false
% 3.14/0.96  --prop_solver_per_cl                    1000
% 3.14/0.96  --min_unsat_core                        false
% 3.14/0.96  --soft_assumptions                      false
% 3.14/0.96  --soft_lemma_size                       3
% 3.14/0.96  --prop_impl_unit_size                   0
% 3.14/0.96  --prop_impl_unit                        []
% 3.14/0.96  --share_sel_clauses                     true
% 3.14/0.96  --reset_solvers                         false
% 3.14/0.96  --bc_imp_inh                            [conj_cone]
% 3.14/0.96  --conj_cone_tolerance                   3.
% 3.14/0.96  --extra_neg_conj                        none
% 3.14/0.96  --large_theory_mode                     true
% 3.14/0.96  --prolific_symb_bound                   200
% 3.14/0.96  --lt_threshold                          2000
% 3.14/0.96  --clause_weak_htbl                      true
% 3.14/0.96  --gc_record_bc_elim                     false
% 3.14/0.96  
% 3.14/0.96  ------ Preprocessing Options
% 3.14/0.96  
% 3.14/0.96  --preprocessing_flag                    true
% 3.14/0.96  --time_out_prep_mult                    0.1
% 3.14/0.96  --splitting_mode                        input
% 3.14/0.96  --splitting_grd                         true
% 3.14/0.96  --splitting_cvd                         false
% 3.14/0.96  --splitting_cvd_svl                     false
% 3.14/0.96  --splitting_nvd                         32
% 3.14/0.96  --sub_typing                            true
% 3.14/0.96  --prep_gs_sim                           true
% 3.14/0.96  --prep_unflatten                        true
% 3.14/0.96  --prep_res_sim                          true
% 3.14/0.96  --prep_upred                            true
% 3.14/0.96  --prep_sem_filter                       exhaustive
% 3.14/0.96  --prep_sem_filter_out                   false
% 3.14/0.96  --pred_elim                             true
% 3.14/0.96  --res_sim_input                         true
% 3.14/0.96  --eq_ax_congr_red                       true
% 3.14/0.96  --pure_diseq_elim                       true
% 3.14/0.96  --brand_transform                       false
% 3.14/0.96  --non_eq_to_eq                          false
% 3.14/0.96  --prep_def_merge                        true
% 3.14/0.96  --prep_def_merge_prop_impl              false
% 3.14/0.96  --prep_def_merge_mbd                    true
% 3.14/0.96  --prep_def_merge_tr_red                 false
% 3.14/0.96  --prep_def_merge_tr_cl                  false
% 3.14/0.96  --smt_preprocessing                     true
% 3.14/0.96  --smt_ac_axioms                         fast
% 3.14/0.96  --preprocessed_out                      false
% 3.14/0.96  --preprocessed_stats                    false
% 3.14/0.96  
% 3.14/0.96  ------ Abstraction refinement Options
% 3.14/0.96  
% 3.14/0.96  --abstr_ref                             []
% 3.14/0.96  --abstr_ref_prep                        false
% 3.14/0.96  --abstr_ref_until_sat                   false
% 3.14/0.96  --abstr_ref_sig_restrict                funpre
% 3.14/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.96  --abstr_ref_under                       []
% 3.14/0.96  
% 3.14/0.96  ------ SAT Options
% 3.14/0.96  
% 3.14/0.96  --sat_mode                              false
% 3.14/0.96  --sat_fm_restart_options                ""
% 3.14/0.96  --sat_gr_def                            false
% 3.14/0.96  --sat_epr_types                         true
% 3.14/0.96  --sat_non_cyclic_types                  false
% 3.14/0.96  --sat_finite_models                     false
% 3.14/0.96  --sat_fm_lemmas                         false
% 3.14/0.96  --sat_fm_prep                           false
% 3.14/0.96  --sat_fm_uc_incr                        true
% 3.14/0.96  --sat_out_model                         small
% 3.14/0.96  --sat_out_clauses                       false
% 3.14/0.96  
% 3.14/0.96  ------ QBF Options
% 3.14/0.96  
% 3.14/0.96  --qbf_mode                              false
% 3.14/0.96  --qbf_elim_univ                         false
% 3.14/0.96  --qbf_dom_inst                          none
% 3.14/0.96  --qbf_dom_pre_inst                      false
% 3.14/0.96  --qbf_sk_in                             false
% 3.14/0.96  --qbf_pred_elim                         true
% 3.14/0.96  --qbf_split                             512
% 3.14/0.96  
% 3.14/0.96  ------ BMC1 Options
% 3.14/0.96  
% 3.14/0.96  --bmc1_incremental                      false
% 3.14/0.96  --bmc1_axioms                           reachable_all
% 3.14/0.96  --bmc1_min_bound                        0
% 3.14/0.96  --bmc1_max_bound                        -1
% 3.14/0.96  --bmc1_max_bound_default                -1
% 3.14/0.96  --bmc1_symbol_reachability              true
% 3.14/0.96  --bmc1_property_lemmas                  false
% 3.14/0.96  --bmc1_k_induction                      false
% 3.14/0.96  --bmc1_non_equiv_states                 false
% 3.14/0.96  --bmc1_deadlock                         false
% 3.14/0.96  --bmc1_ucm                              false
% 3.14/0.96  --bmc1_add_unsat_core                   none
% 3.14/0.96  --bmc1_unsat_core_children              false
% 3.14/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.96  --bmc1_out_stat                         full
% 3.14/0.96  --bmc1_ground_init                      false
% 3.14/0.96  --bmc1_pre_inst_next_state              false
% 3.14/0.96  --bmc1_pre_inst_state                   false
% 3.14/0.96  --bmc1_pre_inst_reach_state             false
% 3.14/0.96  --bmc1_out_unsat_core                   false
% 3.14/0.96  --bmc1_aig_witness_out                  false
% 3.14/0.96  --bmc1_verbose                          false
% 3.14/0.96  --bmc1_dump_clauses_tptp                false
% 3.14/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.96  --bmc1_dump_file                        -
% 3.14/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.96  --bmc1_ucm_extend_mode                  1
% 3.14/0.96  --bmc1_ucm_init_mode                    2
% 3.14/0.96  --bmc1_ucm_cone_mode                    none
% 3.14/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.96  --bmc1_ucm_relax_model                  4
% 3.14/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.96  --bmc1_ucm_layered_model                none
% 3.14/0.96  --bmc1_ucm_max_lemma_size               10
% 3.14/0.96  
% 3.14/0.96  ------ AIG Options
% 3.14/0.96  
% 3.14/0.96  --aig_mode                              false
% 3.14/0.96  
% 3.14/0.96  ------ Instantiation Options
% 3.14/0.96  
% 3.14/0.96  --instantiation_flag                    true
% 3.14/0.96  --inst_sos_flag                         false
% 3.14/0.96  --inst_sos_phase                        true
% 3.14/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.96  --inst_lit_sel_side                     num_symb
% 3.14/0.96  --inst_solver_per_active                1400
% 3.14/0.96  --inst_solver_calls_frac                1.
% 3.14/0.96  --inst_passive_queue_type               priority_queues
% 3.14/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.96  --inst_passive_queues_freq              [25;2]
% 3.14/0.96  --inst_dismatching                      true
% 3.14/0.96  --inst_eager_unprocessed_to_passive     true
% 3.14/0.96  --inst_prop_sim_given                   true
% 3.14/0.96  --inst_prop_sim_new                     false
% 3.14/0.96  --inst_subs_new                         false
% 3.14/0.96  --inst_eq_res_simp                      false
% 3.14/0.96  --inst_subs_given                       false
% 3.14/0.96  --inst_orphan_elimination               true
% 3.14/0.96  --inst_learning_loop_flag               true
% 3.14/0.96  --inst_learning_start                   3000
% 3.14/0.96  --inst_learning_factor                  2
% 3.14/0.96  --inst_start_prop_sim_after_learn       3
% 3.14/0.96  --inst_sel_renew                        solver
% 3.14/0.96  --inst_lit_activity_flag                true
% 3.14/0.96  --inst_restr_to_given                   false
% 3.14/0.96  --inst_activity_threshold               500
% 3.14/0.96  --inst_out_proof                        true
% 3.14/0.96  
% 3.14/0.96  ------ Resolution Options
% 3.14/0.96  
% 3.14/0.96  --resolution_flag                       true
% 3.14/0.96  --res_lit_sel                           adaptive
% 3.14/0.96  --res_lit_sel_side                      none
% 3.14/0.96  --res_ordering                          kbo
% 3.14/0.96  --res_to_prop_solver                    active
% 3.14/0.96  --res_prop_simpl_new                    false
% 3.14/0.96  --res_prop_simpl_given                  true
% 3.14/0.96  --res_passive_queue_type                priority_queues
% 3.14/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.96  --res_passive_queues_freq               [15;5]
% 3.14/0.96  --res_forward_subs                      full
% 3.14/0.96  --res_backward_subs                     full
% 3.14/0.96  --res_forward_subs_resolution           true
% 3.14/0.96  --res_backward_subs_resolution          true
% 3.14/0.96  --res_orphan_elimination                true
% 3.14/0.96  --res_time_limit                        2.
% 3.14/0.96  --res_out_proof                         true
% 3.14/0.96  
% 3.14/0.96  ------ Superposition Options
% 3.14/0.96  
% 3.14/0.96  --superposition_flag                    true
% 3.14/0.96  --sup_passive_queue_type                priority_queues
% 3.14/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.96  --demod_completeness_check              fast
% 3.14/0.96  --demod_use_ground                      true
% 3.14/0.96  --sup_to_prop_solver                    passive
% 3.14/0.96  --sup_prop_simpl_new                    true
% 3.14/0.96  --sup_prop_simpl_given                  true
% 3.14/0.96  --sup_fun_splitting                     false
% 3.14/0.96  --sup_smt_interval                      50000
% 3.14/0.96  
% 3.14/0.96  ------ Superposition Simplification Setup
% 3.14/0.96  
% 3.14/0.96  --sup_indices_passive                   []
% 3.14/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.96  --sup_full_bw                           [BwDemod]
% 3.14/0.96  --sup_immed_triv                        [TrivRules]
% 3.14/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.96  --sup_immed_bw_main                     []
% 3.14/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.96  
% 3.14/0.96  ------ Combination Options
% 3.14/0.96  
% 3.14/0.96  --comb_res_mult                         3
% 3.14/0.96  --comb_sup_mult                         2
% 3.14/0.96  --comb_inst_mult                        10
% 3.14/0.96  
% 3.14/0.96  ------ Debug Options
% 3.14/0.96  
% 3.14/0.96  --dbg_backtrace                         false
% 3.14/0.96  --dbg_dump_prop_clauses                 false
% 3.14/0.96  --dbg_dump_prop_clauses_file            -
% 3.14/0.96  --dbg_out_stat                          false
% 3.14/0.96  ------ Parsing...
% 3.14/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.96  
% 3.14/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.14/0.96  
% 3.14/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.96  
% 3.14/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.96  ------ Proving...
% 3.14/0.96  ------ Problem Properties 
% 3.14/0.96  
% 3.14/0.96  
% 3.14/0.96  clauses                                 24
% 3.14/0.96  conjectures                             3
% 3.14/0.96  EPR                                     2
% 3.14/0.96  Horn                                    15
% 3.14/0.96  unary                                   4
% 3.14/0.96  binary                                  6
% 3.14/0.96  lits                                    71
% 3.14/0.96  lits eq                                 31
% 3.14/0.96  fd_pure                                 0
% 3.14/0.96  fd_pseudo                               0
% 3.14/0.96  fd_cond                                 4
% 3.14/0.96  fd_pseudo_cond                          0
% 3.14/0.96  AC symbols                              0
% 3.14/0.96  
% 3.14/0.96  ------ Schedule dynamic 5 is on 
% 3.14/0.96  
% 3.14/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/0.96  
% 3.14/0.96  
% 3.14/0.96  ------ 
% 3.14/0.96  Current options:
% 3.14/0.96  ------ 
% 3.14/0.96  
% 3.14/0.96  ------ Input Options
% 3.14/0.96  
% 3.14/0.96  --out_options                           all
% 3.14/0.96  --tptp_safe_out                         true
% 3.14/0.96  --problem_path                          ""
% 3.14/0.96  --include_path                          ""
% 3.14/0.96  --clausifier                            res/vclausify_rel
% 3.14/0.96  --clausifier_options                    --mode clausify
% 3.14/0.96  --stdin                                 false
% 3.14/0.96  --stats_out                             all
% 3.14/0.96  
% 3.14/0.96  ------ General Options
% 3.14/0.96  
% 3.14/0.96  --fof                                   false
% 3.14/0.96  --time_out_real                         305.
% 3.14/0.96  --time_out_virtual                      -1.
% 3.14/0.96  --symbol_type_check                     false
% 3.14/0.96  --clausify_out                          false
% 3.14/0.96  --sig_cnt_out                           false
% 3.14/0.96  --trig_cnt_out                          false
% 3.14/0.96  --trig_cnt_out_tolerance                1.
% 3.14/0.96  --trig_cnt_out_sk_spl                   false
% 3.14/0.96  --abstr_cl_out                          false
% 3.14/0.96  
% 3.14/0.96  ------ Global Options
% 3.14/0.96  
% 3.14/0.96  --schedule                              default
% 3.14/0.96  --add_important_lit                     false
% 3.14/0.96  --prop_solver_per_cl                    1000
% 3.14/0.96  --min_unsat_core                        false
% 3.14/0.96  --soft_assumptions                      false
% 3.14/0.96  --soft_lemma_size                       3
% 3.14/0.96  --prop_impl_unit_size                   0
% 3.14/0.96  --prop_impl_unit                        []
% 3.14/0.96  --share_sel_clauses                     true
% 3.14/0.96  --reset_solvers                         false
% 3.14/0.96  --bc_imp_inh                            [conj_cone]
% 3.14/0.96  --conj_cone_tolerance                   3.
% 3.14/0.96  --extra_neg_conj                        none
% 3.14/0.96  --large_theory_mode                     true
% 3.14/0.96  --prolific_symb_bound                   200
% 3.14/0.96  --lt_threshold                          2000
% 3.14/0.96  --clause_weak_htbl                      true
% 3.14/0.96  --gc_record_bc_elim                     false
% 3.14/0.96  
% 3.14/0.96  ------ Preprocessing Options
% 3.14/0.96  
% 3.14/0.96  --preprocessing_flag                    true
% 3.14/0.96  --time_out_prep_mult                    0.1
% 3.14/0.96  --splitting_mode                        input
% 3.14/0.96  --splitting_grd                         true
% 3.14/0.96  --splitting_cvd                         false
% 3.14/0.96  --splitting_cvd_svl                     false
% 3.14/0.96  --splitting_nvd                         32
% 3.14/0.96  --sub_typing                            true
% 3.14/0.96  --prep_gs_sim                           true
% 3.14/0.96  --prep_unflatten                        true
% 3.14/0.96  --prep_res_sim                          true
% 3.14/0.96  --prep_upred                            true
% 3.14/0.96  --prep_sem_filter                       exhaustive
% 3.14/0.96  --prep_sem_filter_out                   false
% 3.14/0.96  --pred_elim                             true
% 3.14/0.96  --res_sim_input                         true
% 3.14/0.96  --eq_ax_congr_red                       true
% 3.14/0.96  --pure_diseq_elim                       true
% 3.14/0.96  --brand_transform                       false
% 3.14/0.96  --non_eq_to_eq                          false
% 3.14/0.96  --prep_def_merge                        true
% 3.14/0.96  --prep_def_merge_prop_impl              false
% 3.14/0.96  --prep_def_merge_mbd                    true
% 3.14/0.96  --prep_def_merge_tr_red                 false
% 3.14/0.96  --prep_def_merge_tr_cl                  false
% 3.14/0.96  --smt_preprocessing                     true
% 3.14/0.96  --smt_ac_axioms                         fast
% 3.14/0.96  --preprocessed_out                      false
% 3.14/0.96  --preprocessed_stats                    false
% 3.14/0.96  
% 3.14/0.96  ------ Abstraction refinement Options
% 3.14/0.96  
% 3.14/0.96  --abstr_ref                             []
% 3.14/0.96  --abstr_ref_prep                        false
% 3.14/0.96  --abstr_ref_until_sat                   false
% 3.14/0.96  --abstr_ref_sig_restrict                funpre
% 3.14/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.96  --abstr_ref_under                       []
% 3.14/0.96  
% 3.14/0.96  ------ SAT Options
% 3.14/0.96  
% 3.14/0.96  --sat_mode                              false
% 3.14/0.96  --sat_fm_restart_options                ""
% 3.14/0.96  --sat_gr_def                            false
% 3.14/0.96  --sat_epr_types                         true
% 3.14/0.96  --sat_non_cyclic_types                  false
% 3.14/0.96  --sat_finite_models                     false
% 3.14/0.96  --sat_fm_lemmas                         false
% 3.14/0.96  --sat_fm_prep                           false
% 3.14/0.96  --sat_fm_uc_incr                        true
% 3.14/0.96  --sat_out_model                         small
% 3.14/0.96  --sat_out_clauses                       false
% 3.14/0.96  
% 3.14/0.96  ------ QBF Options
% 3.14/0.96  
% 3.14/0.96  --qbf_mode                              false
% 3.14/0.96  --qbf_elim_univ                         false
% 3.14/0.96  --qbf_dom_inst                          none
% 3.14/0.96  --qbf_dom_pre_inst                      false
% 3.14/0.96  --qbf_sk_in                             false
% 3.14/0.96  --qbf_pred_elim                         true
% 3.14/0.96  --qbf_split                             512
% 3.14/0.96  
% 3.14/0.96  ------ BMC1 Options
% 3.14/0.96  
% 3.14/0.96  --bmc1_incremental                      false
% 3.14/0.96  --bmc1_axioms                           reachable_all
% 3.14/0.96  --bmc1_min_bound                        0
% 3.14/0.96  --bmc1_max_bound                        -1
% 3.14/0.96  --bmc1_max_bound_default                -1
% 3.14/0.96  --bmc1_symbol_reachability              true
% 3.14/0.96  --bmc1_property_lemmas                  false
% 3.14/0.96  --bmc1_k_induction                      false
% 3.14/0.96  --bmc1_non_equiv_states                 false
% 3.14/0.96  --bmc1_deadlock                         false
% 3.14/0.96  --bmc1_ucm                              false
% 3.14/0.96  --bmc1_add_unsat_core                   none
% 3.14/0.96  --bmc1_unsat_core_children              false
% 3.14/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.96  --bmc1_out_stat                         full
% 3.14/0.96  --bmc1_ground_init                      false
% 3.14/0.96  --bmc1_pre_inst_next_state              false
% 3.14/0.96  --bmc1_pre_inst_state                   false
% 3.14/0.96  --bmc1_pre_inst_reach_state             false
% 3.14/0.96  --bmc1_out_unsat_core                   false
% 3.14/0.96  --bmc1_aig_witness_out                  false
% 3.14/0.96  --bmc1_verbose                          false
% 3.14/0.96  --bmc1_dump_clauses_tptp                false
% 3.14/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.96  --bmc1_dump_file                        -
% 3.14/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.96  --bmc1_ucm_extend_mode                  1
% 3.14/0.96  --bmc1_ucm_init_mode                    2
% 3.14/0.96  --bmc1_ucm_cone_mode                    none
% 3.14/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.96  --bmc1_ucm_relax_model                  4
% 3.14/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.96  --bmc1_ucm_layered_model                none
% 3.14/0.96  --bmc1_ucm_max_lemma_size               10
% 3.14/0.96  
% 3.14/0.96  ------ AIG Options
% 3.14/0.96  
% 3.14/0.96  --aig_mode                              false
% 3.14/0.96  
% 3.14/0.96  ------ Instantiation Options
% 3.14/0.96  
% 3.14/0.96  --instantiation_flag                    true
% 3.14/0.96  --inst_sos_flag                         false
% 3.14/0.96  --inst_sos_phase                        true
% 3.14/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.96  --inst_lit_sel_side                     none
% 3.14/0.96  --inst_solver_per_active                1400
% 3.14/0.96  --inst_solver_calls_frac                1.
% 3.14/0.96  --inst_passive_queue_type               priority_queues
% 3.14/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.96  --inst_passive_queues_freq              [25;2]
% 3.14/0.96  --inst_dismatching                      true
% 3.14/0.96  --inst_eager_unprocessed_to_passive     true
% 3.14/0.96  --inst_prop_sim_given                   true
% 3.14/0.96  --inst_prop_sim_new                     false
% 3.14/0.96  --inst_subs_new                         false
% 3.14/0.96  --inst_eq_res_simp                      false
% 3.14/0.96  --inst_subs_given                       false
% 3.14/0.96  --inst_orphan_elimination               true
% 3.14/0.96  --inst_learning_loop_flag               true
% 3.14/0.96  --inst_learning_start                   3000
% 3.14/0.96  --inst_learning_factor                  2
% 3.14/0.96  --inst_start_prop_sim_after_learn       3
% 3.14/0.96  --inst_sel_renew                        solver
% 3.14/0.96  --inst_lit_activity_flag                true
% 3.14/0.96  --inst_restr_to_given                   false
% 3.14/0.96  --inst_activity_threshold               500
% 3.14/0.96  --inst_out_proof                        true
% 3.14/0.96  
% 3.14/0.96  ------ Resolution Options
% 3.14/0.96  
% 3.14/0.96  --resolution_flag                       false
% 3.14/0.96  --res_lit_sel                           adaptive
% 3.14/0.96  --res_lit_sel_side                      none
% 3.14/0.96  --res_ordering                          kbo
% 3.14/0.96  --res_to_prop_solver                    active
% 3.14/0.96  --res_prop_simpl_new                    false
% 3.14/0.96  --res_prop_simpl_given                  true
% 3.14/0.96  --res_passive_queue_type                priority_queues
% 3.14/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.96  --res_passive_queues_freq               [15;5]
% 3.14/0.96  --res_forward_subs                      full
% 3.14/0.96  --res_backward_subs                     full
% 3.14/0.96  --res_forward_subs_resolution           true
% 3.14/0.96  --res_backward_subs_resolution          true
% 3.14/0.96  --res_orphan_elimination                true
% 3.14/0.96  --res_time_limit                        2.
% 3.14/0.96  --res_out_proof                         true
% 3.14/0.96  
% 3.14/0.96  ------ Superposition Options
% 3.14/0.96  
% 3.14/0.96  --superposition_flag                    true
% 3.14/0.96  --sup_passive_queue_type                priority_queues
% 3.14/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.96  --demod_completeness_check              fast
% 3.14/0.96  --demod_use_ground                      true
% 3.14/0.96  --sup_to_prop_solver                    passive
% 3.14/0.96  --sup_prop_simpl_new                    true
% 3.14/0.96  --sup_prop_simpl_given                  true
% 3.14/0.96  --sup_fun_splitting                     false
% 3.14/0.96  --sup_smt_interval                      50000
% 3.14/0.96  
% 3.14/0.96  ------ Superposition Simplification Setup
% 3.14/0.96  
% 3.14/0.96  --sup_indices_passive                   []
% 3.14/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.96  --sup_full_bw                           [BwDemod]
% 3.14/0.96  --sup_immed_triv                        [TrivRules]
% 3.14/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.96  --sup_immed_bw_main                     []
% 3.14/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.96  
% 3.14/0.96  ------ Combination Options
% 3.14/0.96  
% 3.14/0.96  --comb_res_mult                         3
% 3.14/0.96  --comb_sup_mult                         2
% 3.14/0.96  --comb_inst_mult                        10
% 3.14/0.96  
% 3.14/0.96  ------ Debug Options
% 3.14/0.96  
% 3.14/0.96  --dbg_backtrace                         false
% 3.14/0.96  --dbg_dump_prop_clauses                 false
% 3.14/0.96  --dbg_dump_prop_clauses_file            -
% 3.14/0.96  --dbg_out_stat                          false
% 3.14/0.96  
% 3.14/0.96  
% 3.14/0.96  
% 3.14/0.96  
% 3.14/0.96  ------ Proving...
% 3.14/0.96  
% 3.14/0.96  
% 3.14/0.96  % SZS status Theorem for theBenchmark.p
% 3.14/0.96  
% 3.14/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.96  
% 3.14/0.96  fof(f9,axiom,(
% 3.14/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f21,plain,(
% 3.14/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.96    inference(ennf_transformation,[],[f9])).
% 3.14/0.96  
% 3.14/0.96  fof(f22,plain,(
% 3.14/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.96    inference(flattening,[],[f21])).
% 3.14/0.96  
% 3.14/0.96  fof(f33,plain,(
% 3.14/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.96    inference(nnf_transformation,[],[f22])).
% 3.14/0.96  
% 3.14/0.96  fof(f51,plain,(
% 3.14/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.96    inference(cnf_transformation,[],[f33])).
% 3.14/0.96  
% 3.14/0.96  fof(f11,conjecture,(
% 3.14/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f12,negated_conjecture,(
% 3.14/0.96    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.14/0.96    inference(negated_conjecture,[],[f11])).
% 3.14/0.96  
% 3.14/0.96  fof(f25,plain,(
% 3.14/0.96    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 3.14/0.96    inference(ennf_transformation,[],[f12])).
% 3.14/0.96  
% 3.14/0.96  fof(f26,plain,(
% 3.14/0.96    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 3.14/0.96    inference(flattening,[],[f25])).
% 3.14/0.96  
% 3.14/0.96  fof(f36,plain,(
% 3.14/0.96    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 3.14/0.96    introduced(choice_axiom,[])).
% 3.14/0.96  
% 3.14/0.96  fof(f37,plain,(
% 3.14/0.96    ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 3.14/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f26,f36])).
% 3.14/0.96  
% 3.14/0.96  fof(f60,plain,(
% 3.14/0.96    v1_funct_2(sK7,sK5,sK6)),
% 3.14/0.96    inference(cnf_transformation,[],[f37])).
% 3.14/0.96  
% 3.14/0.96  fof(f61,plain,(
% 3.14/0.96    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.14/0.96    inference(cnf_transformation,[],[f37])).
% 3.14/0.96  
% 3.14/0.96  fof(f7,axiom,(
% 3.14/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f19,plain,(
% 3.14/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.96    inference(ennf_transformation,[],[f7])).
% 3.14/0.96  
% 3.14/0.96  fof(f49,plain,(
% 3.14/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.96    inference(cnf_transformation,[],[f19])).
% 3.14/0.96  
% 3.14/0.96  fof(f6,axiom,(
% 3.14/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f17,plain,(
% 3.14/0.96    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.14/0.96    inference(ennf_transformation,[],[f6])).
% 3.14/0.96  
% 3.14/0.96  fof(f18,plain,(
% 3.14/0.96    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.96    inference(flattening,[],[f17])).
% 3.14/0.96  
% 3.14/0.96  fof(f27,plain,(
% 3.14/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.96    inference(nnf_transformation,[],[f18])).
% 3.14/0.96  
% 3.14/0.96  fof(f28,plain,(
% 3.14/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.96    inference(rectify,[],[f27])).
% 3.14/0.96  
% 3.14/0.96  fof(f31,plain,(
% 3.14/0.96    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 3.14/0.96    introduced(choice_axiom,[])).
% 3.14/0.96  
% 3.14/0.96  fof(f30,plain,(
% 3.14/0.96    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 3.14/0.96    introduced(choice_axiom,[])).
% 3.14/0.96  
% 3.14/0.96  fof(f29,plain,(
% 3.14/0.96    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 3.14/0.96    introduced(choice_axiom,[])).
% 3.14/0.96  
% 3.14/0.96  fof(f32,plain,(
% 3.14/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31,f30,f29])).
% 3.14/0.96  
% 3.14/0.96  fof(f43,plain,(
% 3.14/0.96    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.96    inference(cnf_transformation,[],[f32])).
% 3.14/0.96  
% 3.14/0.96  fof(f67,plain,(
% 3.14/0.96    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.96    inference(equality_resolution,[],[f43])).
% 3.14/0.96  
% 3.14/0.96  fof(f59,plain,(
% 3.14/0.96    v1_funct_1(sK7)),
% 3.14/0.96    inference(cnf_transformation,[],[f37])).
% 3.14/0.96  
% 3.14/0.96  fof(f3,axiom,(
% 3.14/0.96    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f15,plain,(
% 3.14/0.96    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.14/0.96    inference(ennf_transformation,[],[f3])).
% 3.14/0.96  
% 3.14/0.96  fof(f40,plain,(
% 3.14/0.96    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.14/0.96    inference(cnf_transformation,[],[f15])).
% 3.14/0.96  
% 3.14/0.96  fof(f4,axiom,(
% 3.14/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f16,plain,(
% 3.14/0.96    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.14/0.96    inference(ennf_transformation,[],[f4])).
% 3.14/0.96  
% 3.14/0.96  fof(f41,plain,(
% 3.14/0.96    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.14/0.96    inference(cnf_transformation,[],[f16])).
% 3.14/0.96  
% 3.14/0.96  fof(f5,axiom,(
% 3.14/0.96    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f42,plain,(
% 3.14/0.96    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.14/0.96    inference(cnf_transformation,[],[f5])).
% 3.14/0.96  
% 3.14/0.96  fof(f62,plain,(
% 3.14/0.96    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))),
% 3.14/0.96    inference(cnf_transformation,[],[f37])).
% 3.14/0.96  
% 3.14/0.96  fof(f10,axiom,(
% 3.14/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f23,plain,(
% 3.14/0.96    ! [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : (k1_funct_1(X2,X4) != X3 | ~r2_hidden(X4,X0)) & r2_hidden(X3,X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.14/0.96    inference(ennf_transformation,[],[f10])).
% 3.14/0.96  
% 3.14/0.96  fof(f24,plain,(
% 3.14/0.96    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : (k1_funct_1(X2,X4) != X3 | ~r2_hidden(X4,X0)) & r2_hidden(X3,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.14/0.96    inference(flattening,[],[f23])).
% 3.14/0.96  
% 3.14/0.96  fof(f34,plain,(
% 3.14/0.96    ! [X2,X1,X0] : (? [X3] : (! [X4] : (k1_funct_1(X2,X4) != X3 | ~r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => (! [X4] : (k1_funct_1(X2,X4) != sK3(X0,X1,X2) | ~r2_hidden(X4,X0)) & r2_hidden(sK3(X0,X1,X2),X1)))),
% 3.14/0.96    introduced(choice_axiom,[])).
% 3.14/0.96  
% 3.14/0.96  fof(f35,plain,(
% 3.14/0.96    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = X1 | (! [X4] : (k1_funct_1(X2,X4) != sK3(X0,X1,X2) | ~r2_hidden(X4,X0)) & r2_hidden(sK3(X0,X1,X2),X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.14/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f34])).
% 3.14/0.96  
% 3.14/0.96  fof(f57,plain,(
% 3.14/0.96    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.14/0.96    inference(cnf_transformation,[],[f35])).
% 3.14/0.96  
% 3.14/0.96  fof(f8,axiom,(
% 3.14/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f20,plain,(
% 3.14/0.96    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.96    inference(ennf_transformation,[],[f8])).
% 3.14/0.96  
% 3.14/0.96  fof(f50,plain,(
% 3.14/0.96    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.96    inference(cnf_transformation,[],[f20])).
% 3.14/0.96  
% 3.14/0.96  fof(f44,plain,(
% 3.14/0.96    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.96    inference(cnf_transformation,[],[f32])).
% 3.14/0.96  
% 3.14/0.96  fof(f66,plain,(
% 3.14/0.96    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.96    inference(equality_resolution,[],[f44])).
% 3.14/0.96  
% 3.14/0.96  fof(f1,axiom,(
% 3.14/0.96    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f13,plain,(
% 3.14/0.96    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.14/0.96    inference(unused_predicate_definition_removal,[],[f1])).
% 3.14/0.96  
% 3.14/0.96  fof(f14,plain,(
% 3.14/0.96    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.14/0.96    inference(ennf_transformation,[],[f13])).
% 3.14/0.96  
% 3.14/0.96  fof(f38,plain,(
% 3.14/0.96    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.14/0.96    inference(cnf_transformation,[],[f14])).
% 3.14/0.96  
% 3.14/0.96  fof(f2,axiom,(
% 3.14/0.96    v1_xboole_0(k1_xboole_0)),
% 3.14/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.96  
% 3.14/0.96  fof(f39,plain,(
% 3.14/0.96    v1_xboole_0(k1_xboole_0)),
% 3.14/0.96    inference(cnf_transformation,[],[f2])).
% 3.14/0.96  
% 3.14/0.96  fof(f63,plain,(
% 3.14/0.96    ( ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) )),
% 3.14/0.96    inference(cnf_transformation,[],[f37])).
% 3.14/0.96  
% 3.14/0.96  cnf(c_18,plain,
% 3.14/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.14/0.96      | k1_xboole_0 = X2 ),
% 3.14/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_24,negated_conjecture,
% 3.14/0.96      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.14/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1048,plain,
% 3.14/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.14/0.96      | sK6 != X2
% 3.14/0.96      | sK5 != X1
% 3.14/0.96      | sK7 != X0
% 3.14/0.96      | k1_xboole_0 = X2 ),
% 3.14/0.96      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1049,plain,
% 3.14/0.96      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.14/0.96      | k1_relset_1(sK5,sK6,sK7) = sK5
% 3.14/0.96      | k1_xboole_0 = sK6 ),
% 3.14/0.96      inference(unflattening,[status(thm)],[c_1048]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_23,negated_conjecture,
% 3.14/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.14/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1051,plain,
% 3.14/0.96      ( k1_relset_1(sK5,sK6,sK7) = sK5 | k1_xboole_0 = sK6 ),
% 3.14/0.96      inference(global_propositional_subsumption,
% 3.14/0.96                [status(thm)],
% 3.14/0.96                [c_1049,c_23]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1756,plain,
% 3.14/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_11,plain,
% 3.14/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.14/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1760,plain,
% 3.14/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.14/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2298,plain,
% 3.14/0.96      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 3.14/0.96      inference(superposition,[status(thm)],[c_1756,c_1760]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2362,plain,
% 3.14/0.96      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 3.14/0.96      inference(superposition,[status(thm)],[c_1051,c_2298]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_10,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.14/0.96      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 3.14/0.96      | ~ v1_funct_1(X1)
% 3.14/0.96      | ~ v1_relat_1(X1) ),
% 3.14/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_25,negated_conjecture,
% 3.14/0.96      ( v1_funct_1(sK7) ),
% 3.14/0.96      inference(cnf_transformation,[],[f59]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_304,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.14/0.96      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 3.14/0.96      | ~ v1_relat_1(X1)
% 3.14/0.96      | sK7 != X1 ),
% 3.14/0.96      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_305,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 3.14/0.96      | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7))
% 3.14/0.96      | ~ v1_relat_1(sK7) ),
% 3.14/0.96      inference(unflattening,[status(thm)],[c_304]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1754,plain,
% 3.14/0.96      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.14/0.96      | r2_hidden(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.14/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2,plain,
% 3.14/0.96      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.14/0.96      inference(cnf_transformation,[],[f40]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1763,plain,
% 3.14/0.96      ( m1_subset_1(X0,X1) = iProver_top
% 3.14/0.96      | r2_hidden(X0,X1) != iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2153,plain,
% 3.14/0.96      ( m1_subset_1(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.14/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.14/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.14/0.96      inference(superposition,[status(thm)],[c_1754,c_1763]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_28,plain,
% 3.14/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_3,plain,
% 3.14/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.14/0.96      | ~ v1_relat_1(X1)
% 3.14/0.96      | v1_relat_1(X0) ),
% 3.14/0.96      inference(cnf_transformation,[],[f41]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1967,plain,
% 3.14/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.96      | v1_relat_1(X0)
% 3.14/0.96      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2066,plain,
% 3.14/0.96      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.14/0.96      | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
% 3.14/0.96      | v1_relat_1(sK7) ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_1967]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2067,plain,
% 3.14/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.14/0.96      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.14/0.96      | v1_relat_1(sK7) = iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_2066]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_4,plain,
% 3.14/0.96      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2092,plain,
% 3.14/0.96      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_4]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2093,plain,
% 3.14/0.96      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_2092]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_3075,plain,
% 3.14/0.96      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.14/0.96      | m1_subset_1(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 3.14/0.96      inference(global_propositional_subsumption,
% 3.14/0.96                [status(thm)],
% 3.14/0.96                [c_2153,c_28,c_2067,c_2093]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_3076,plain,
% 3.14/0.96      ( m1_subset_1(sK2(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.14/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.14/0.96      inference(renaming,[status(thm)],[c_3075]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_3083,plain,
% 3.14/0.96      ( sK6 = k1_xboole_0
% 3.14/0.96      | m1_subset_1(sK2(sK7,X0),sK5) = iProver_top
% 3.14/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.14/0.96      inference(superposition,[status(thm)],[c_2362,c_3076]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_22,negated_conjecture,
% 3.14/0.96      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
% 3.14/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_20,plain,
% 3.14/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.96      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.14/0.96      | ~ v1_funct_1(X0)
% 3.14/0.96      | k2_relset_1(X1,X2,X0) = X2 ),
% 3.14/0.96      inference(cnf_transformation,[],[f57]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_370,plain,
% 3.14/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.96      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.14/0.96      | k2_relset_1(X1,X2,X0) = X2
% 3.14/0.96      | sK7 != X0 ),
% 3.14/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_371,plain,
% 3.14/0.96      ( ~ v1_funct_2(sK7,X0,X1)
% 3.14/0.96      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.96      | r2_hidden(sK3(X0,X1,sK7),X1)
% 3.14/0.96      | k2_relset_1(X0,X1,sK7) = X1 ),
% 3.14/0.96      inference(unflattening,[status(thm)],[c_370]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1121,plain,
% 3.14/0.96      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.96      | r2_hidden(sK3(X0,X1,sK7),X1)
% 3.14/0.96      | k2_relset_1(X0,X1,sK7) = X1
% 3.14/0.96      | sK6 != X1
% 3.14/0.96      | sK5 != X0
% 3.14/0.96      | sK7 != sK7 ),
% 3.14/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_371]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1122,plain,
% 3.14/0.96      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.14/0.96      | r2_hidden(sK3(sK5,sK6,sK7),sK6)
% 3.14/0.96      | k2_relset_1(sK5,sK6,sK7) = sK6 ),
% 3.14/0.96      inference(unflattening,[status(thm)],[c_1121]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1338,plain,( X0 = X0 ),theory(equality) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1369,plain,
% 3.14/0.96      ( k1_xboole_0 = k1_xboole_0 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_1338]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1339,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2321,plain,
% 3.14/0.96      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_1339]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2322,plain,
% 3.14/0.96      ( sK6 != k1_xboole_0
% 3.14/0.96      | k1_xboole_0 = sK6
% 3.14/0.96      | k1_xboole_0 != k1_xboole_0 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_2321]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_12,plain,
% 3.14/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.14/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1759,plain,
% 3.14/0.96      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.14/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2185,plain,
% 3.14/0.96      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 3.14/0.96      inference(superposition,[status(thm)],[c_1756,c_1759]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1757,plain,
% 3.14/0.96      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2301,plain,
% 3.14/0.96      ( r2_hidden(sK4,k2_relat_1(sK7)) = iProver_top ),
% 3.14/0.96      inference(demodulation,[status(thm)],[c_2185,c_1757]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_9,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.14/0.96      | ~ v1_funct_1(X1)
% 3.14/0.96      | ~ v1_relat_1(X1)
% 3.14/0.96      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 3.14/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_319,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.14/0.96      | ~ v1_relat_1(X1)
% 3.14/0.96      | k1_funct_1(X1,sK2(X1,X0)) = X0
% 3.14/0.96      | sK7 != X1 ),
% 3.14/0.96      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_320,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 3.14/0.96      | ~ v1_relat_1(sK7)
% 3.14/0.96      | k1_funct_1(sK7,sK2(sK7,X0)) = X0 ),
% 3.14/0.96      inference(unflattening,[status(thm)],[c_319]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1753,plain,
% 3.14/0.96      ( k1_funct_1(sK7,sK2(sK7,X0)) = X0
% 3.14/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.14/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2352,plain,
% 3.14/0.96      ( k1_funct_1(sK7,sK2(sK7,sK4)) = sK4
% 3.14/0.96      | v1_relat_1(sK7) != iProver_top ),
% 3.14/0.96      inference(superposition,[status(thm)],[c_2301,c_1753]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2122,plain,
% 3.14/0.96      ( X0 != X1
% 3.14/0.96      | X0 = k2_relset_1(sK5,sK6,sK7)
% 3.14/0.96      | k2_relset_1(sK5,sK6,sK7) != X1 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_1339]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2397,plain,
% 3.14/0.96      ( X0 = k2_relset_1(sK5,sK6,sK7)
% 3.14/0.96      | X0 != sK6
% 3.14/0.96      | k2_relset_1(sK5,sK6,sK7) != sK6 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_2122]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2398,plain,
% 3.14/0.96      ( k2_relset_1(sK5,sK6,sK7) != sK6
% 3.14/0.96      | k1_xboole_0 = k2_relset_1(sK5,sK6,sK7)
% 3.14/0.96      | k1_xboole_0 != sK6 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_2397]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1340,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.14/0.96      theory(equality) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1993,plain,
% 3.14/0.96      ( r2_hidden(X0,X1)
% 3.14/0.96      | ~ r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
% 3.14/0.96      | X1 != k2_relset_1(sK5,sK6,sK7)
% 3.14/0.96      | X0 != sK4 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_1340]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2712,plain,
% 3.14/0.96      ( r2_hidden(k1_funct_1(sK7,sK2(sK7,sK4)),X0)
% 3.14/0.96      | ~ r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
% 3.14/0.96      | X0 != k2_relset_1(sK5,sK6,sK7)
% 3.14/0.96      | k1_funct_1(sK7,sK2(sK7,sK4)) != sK4 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_1993]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2714,plain,
% 3.14/0.96      ( r2_hidden(k1_funct_1(sK7,sK2(sK7,sK4)),k1_xboole_0)
% 3.14/0.96      | ~ r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
% 3.14/0.96      | k1_funct_1(sK7,sK2(sK7,sK4)) != sK4
% 3.14/0.96      | k1_xboole_0 != k2_relset_1(sK5,sK6,sK7) ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_2712]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2606,plain,
% 3.14/0.96      ( r2_hidden(X0,X1)
% 3.14/0.96      | ~ r2_hidden(sK3(sK5,sK6,sK7),sK6)
% 3.14/0.96      | X0 != sK3(sK5,sK6,sK7)
% 3.14/0.96      | X1 != sK6 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_1340]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2906,plain,
% 3.14/0.96      ( r2_hidden(sK3(sK5,sK6,sK7),X0)
% 3.14/0.96      | ~ r2_hidden(sK3(sK5,sK6,sK7),sK6)
% 3.14/0.96      | X0 != sK6
% 3.14/0.96      | sK3(sK5,sK6,sK7) != sK3(sK5,sK6,sK7) ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_2606]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2909,plain,
% 3.14/0.96      ( ~ r2_hidden(sK3(sK5,sK6,sK7),sK6)
% 3.14/0.96      | r2_hidden(sK3(sK5,sK6,sK7),k1_xboole_0)
% 3.14/0.96      | sK3(sK5,sK6,sK7) != sK3(sK5,sK6,sK7)
% 3.14/0.96      | k1_xboole_0 != sK6 ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_2906]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_2907,plain,
% 3.14/0.96      ( sK3(sK5,sK6,sK7) = sK3(sK5,sK6,sK7) ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_1338]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_0,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.14/0.96      inference(cnf_transformation,[],[f38]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1,plain,
% 3.14/0.96      ( v1_xboole_0(k1_xboole_0) ),
% 3.14/0.96      inference(cnf_transformation,[],[f39]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_293,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.14/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_294,plain,
% 3.14/0.96      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.14/0.96      inference(unflattening,[status(thm)],[c_293]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_3936,plain,
% 3.14/0.96      ( ~ r2_hidden(k1_funct_1(sK7,sK2(sK7,sK4)),k1_xboole_0) ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_294]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_7731,plain,
% 3.14/0.96      ( ~ r2_hidden(sK3(sK5,sK6,sK7),k1_xboole_0) ),
% 3.14/0.96      inference(instantiation,[status(thm)],[c_294]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_11319,plain,
% 3.14/0.96      ( m1_subset_1(sK2(sK7,X0),sK5) = iProver_top
% 3.14/0.96      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.14/0.96      inference(global_propositional_subsumption,
% 3.14/0.96                [status(thm)],
% 3.14/0.96                [c_3083,c_23,c_28,c_22,c_1122,c_1369,c_2067,c_2093,
% 3.14/0.96                 c_2322,c_2352,c_2398,c_2714,c_2909,c_2907,c_3936,c_7731]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_3007,plain,
% 3.14/0.96      ( k1_funct_1(sK7,sK2(sK7,sK4)) = sK4 ),
% 3.14/0.96      inference(global_propositional_subsumption,
% 3.14/0.96                [status(thm)],
% 3.14/0.96                [c_2352,c_28,c_2067,c_2093]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_21,negated_conjecture,
% 3.14/0.96      ( ~ m1_subset_1(X0,sK5) | k1_funct_1(sK7,X0) != sK4 ),
% 3.14/0.96      inference(cnf_transformation,[],[f63]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_1758,plain,
% 3.14/0.96      ( k1_funct_1(sK7,X0) != sK4 | m1_subset_1(X0,sK5) != iProver_top ),
% 3.14/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_3012,plain,
% 3.14/0.96      ( m1_subset_1(sK2(sK7,sK4),sK5) != iProver_top ),
% 3.14/0.96      inference(superposition,[status(thm)],[c_3007,c_1758]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(c_11327,plain,
% 3.14/0.96      ( r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
% 3.14/0.96      inference(superposition,[status(thm)],[c_11319,c_3012]) ).
% 3.14/0.96  
% 3.14/0.96  cnf(contradiction,plain,
% 3.14/0.96      ( $false ),
% 3.14/0.96      inference(minisat,[status(thm)],[c_11327,c_2301]) ).
% 3.14/0.96  
% 3.14/0.96  
% 3.14/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/0.96  
% 3.14/0.96  ------                               Statistics
% 3.14/0.96  
% 3.14/0.96  ------ General
% 3.14/0.96  
% 3.14/0.96  abstr_ref_over_cycles:                  0
% 3.14/0.96  abstr_ref_under_cycles:                 0
% 3.14/0.96  gc_basic_clause_elim:                   0
% 3.14/0.96  forced_gc_time:                         0
% 3.14/0.96  parsing_time:                           0.011
% 3.14/0.96  unif_index_cands_time:                  0.
% 3.14/0.96  unif_index_add_time:                    0.
% 3.14/0.96  orderings_time:                         0.
% 3.14/0.96  out_proof_time:                         0.012
% 3.14/0.96  total_time:                             0.459
% 3.14/0.96  num_of_symbols:                         53
% 3.14/0.96  num_of_terms:                           6954
% 3.14/0.96  
% 3.14/0.96  ------ Preprocessing
% 3.14/0.96  
% 3.14/0.96  num_of_splits:                          0
% 3.14/0.96  num_of_split_atoms:                     0
% 3.14/0.96  num_of_reused_defs:                     0
% 3.14/0.96  num_eq_ax_congr_red:                    19
% 3.14/0.96  num_of_sem_filtered_clauses:            1
% 3.14/0.96  num_of_subtypes:                        0
% 3.14/0.96  monotx_restored_types:                  0
% 3.14/0.96  sat_num_of_epr_types:                   0
% 3.14/0.96  sat_num_of_non_cyclic_types:            0
% 3.14/0.96  sat_guarded_non_collapsed_types:        0
% 3.14/0.96  num_pure_diseq_elim:                    0
% 3.14/0.96  simp_replaced_by:                       0
% 3.14/0.96  res_preprocessed:                       131
% 3.14/0.96  prep_upred:                             0
% 3.14/0.96  prep_unflattend:                        89
% 3.14/0.96  smt_new_axioms:                         0
% 3.14/0.96  pred_elim_cands:                        3
% 3.14/0.96  pred_elim:                              3
% 3.14/0.96  pred_elim_cl:                           2
% 3.14/0.96  pred_elim_cycles:                       6
% 3.14/0.96  merged_defs:                            0
% 3.14/0.96  merged_defs_ncl:                        0
% 3.14/0.96  bin_hyper_res:                          0
% 3.14/0.96  prep_cycles:                            4
% 3.14/0.96  pred_elim_time:                         0.019
% 3.14/0.96  splitting_time:                         0.
% 3.14/0.96  sem_filter_time:                        0.
% 3.14/0.96  monotx_time:                            0.001
% 3.14/0.96  subtype_inf_time:                       0.
% 3.14/0.96  
% 3.14/0.96  ------ Problem properties
% 3.14/0.96  
% 3.14/0.96  clauses:                                24
% 3.14/0.96  conjectures:                            3
% 3.14/0.96  epr:                                    2
% 3.14/0.96  horn:                                   15
% 3.14/0.96  ground:                                 6
% 3.14/0.96  unary:                                  4
% 3.14/0.96  binary:                                 6
% 3.14/0.96  lits:                                   71
% 3.14/0.96  lits_eq:                                31
% 3.14/0.96  fd_pure:                                0
% 3.14/0.96  fd_pseudo:                              0
% 3.14/0.96  fd_cond:                                4
% 3.14/0.96  fd_pseudo_cond:                         0
% 3.14/0.96  ac_symbols:                             0
% 3.14/0.96  
% 3.14/0.96  ------ Propositional Solver
% 3.14/0.96  
% 3.14/0.96  prop_solver_calls:                      32
% 3.14/0.96  prop_fast_solver_calls:                 1456
% 3.14/0.96  smt_solver_calls:                       0
% 3.14/0.96  smt_fast_solver_calls:                  0
% 3.14/0.96  prop_num_of_clauses:                    3579
% 3.14/0.96  prop_preprocess_simplified:             6503
% 3.14/0.96  prop_fo_subsumed:                       74
% 3.14/0.96  prop_solver_time:                       0.
% 3.14/0.96  smt_solver_time:                        0.
% 3.14/0.96  smt_fast_solver_time:                   0.
% 3.14/0.96  prop_fast_solver_time:                  0.
% 3.14/0.96  prop_unsat_core_time:                   0.
% 3.14/0.96  
% 3.14/0.96  ------ QBF
% 3.14/0.96  
% 3.14/0.96  qbf_q_res:                              0
% 3.14/0.96  qbf_num_tautologies:                    0
% 3.14/0.96  qbf_prep_cycles:                        0
% 3.14/0.96  
% 3.14/0.96  ------ BMC1
% 3.14/0.96  
% 3.14/0.96  bmc1_current_bound:                     -1
% 3.14/0.96  bmc1_last_solved_bound:                 -1
% 3.14/0.96  bmc1_unsat_core_size:                   -1
% 3.14/0.96  bmc1_unsat_core_parents_size:           -1
% 3.14/0.96  bmc1_merge_next_fun:                    0
% 3.14/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.14/0.96  
% 3.14/0.96  ------ Instantiation
% 3.14/0.96  
% 3.14/0.96  inst_num_of_clauses:                    745
% 3.14/0.96  inst_num_in_passive:                    216
% 3.14/0.96  inst_num_in_active:                     481
% 3.14/0.96  inst_num_in_unprocessed:                48
% 3.14/0.96  inst_num_of_loops:                      620
% 3.14/0.96  inst_num_of_learning_restarts:          0
% 3.14/0.96  inst_num_moves_active_passive:          133
% 3.14/0.96  inst_lit_activity:                      0
% 3.14/0.96  inst_lit_activity_moves:                0
% 3.14/0.96  inst_num_tautologies:                   0
% 3.14/0.96  inst_num_prop_implied:                  0
% 3.14/0.96  inst_num_existing_simplified:           0
% 3.14/0.96  inst_num_eq_res_simplified:             0
% 3.14/0.96  inst_num_child_elim:                    0
% 3.14/0.96  inst_num_of_dismatching_blockings:      209
% 3.14/0.96  inst_num_of_non_proper_insts:           850
% 3.14/0.96  inst_num_of_duplicates:                 0
% 3.14/0.96  inst_inst_num_from_inst_to_res:         0
% 3.14/0.96  inst_dismatching_checking_time:         0.
% 3.14/0.96  
% 3.14/0.96  ------ Resolution
% 3.14/0.96  
% 3.14/0.96  res_num_of_clauses:                     0
% 3.14/0.96  res_num_in_passive:                     0
% 3.14/0.96  res_num_in_active:                      0
% 3.14/0.96  res_num_of_loops:                       135
% 3.14/0.96  res_forward_subset_subsumed:            64
% 3.14/0.96  res_backward_subset_subsumed:           0
% 3.14/0.96  res_forward_subsumed:                   1
% 3.14/0.96  res_backward_subsumed:                  1
% 3.14/0.96  res_forward_subsumption_resolution:     1
% 3.14/0.96  res_backward_subsumption_resolution:    0
% 3.14/0.96  res_clause_to_clause_subsumption:       2247
% 3.14/0.96  res_orphan_elimination:                 0
% 3.14/0.96  res_tautology_del:                      117
% 3.14/0.96  res_num_eq_res_simplified:              0
% 3.14/0.96  res_num_sel_changes:                    0
% 3.14/0.96  res_moves_from_active_to_pass:          0
% 3.14/0.96  
% 3.14/0.96  ------ Superposition
% 3.14/0.96  
% 3.14/0.96  sup_time_total:                         0.
% 3.14/0.96  sup_time_generating:                    0.
% 3.14/0.96  sup_time_sim_full:                      0.
% 3.14/0.96  sup_time_sim_immed:                     0.
% 3.14/0.96  
% 3.14/0.96  sup_num_of_clauses:                     477
% 3.14/0.96  sup_num_in_active:                      122
% 3.14/0.96  sup_num_in_passive:                     355
% 3.14/0.96  sup_num_of_loops:                       123
% 3.14/0.96  sup_fw_superposition:                   491
% 3.14/0.96  sup_bw_superposition:                   197
% 3.14/0.96  sup_immediate_simplified:               42
% 3.14/0.96  sup_given_eliminated:                   0
% 3.14/0.96  comparisons_done:                       0
% 3.14/0.96  comparisons_avoided:                    56
% 3.14/0.96  
% 3.14/0.96  ------ Simplifications
% 3.14/0.96  
% 3.14/0.96  
% 3.14/0.96  sim_fw_subset_subsumed:                 4
% 3.14/0.96  sim_bw_subset_subsumed:                 0
% 3.14/0.96  sim_fw_subsumed:                        0
% 3.14/0.96  sim_bw_subsumed:                        8
% 3.14/0.96  sim_fw_subsumption_res:                 0
% 3.14/0.96  sim_bw_subsumption_res:                 0
% 3.14/0.96  sim_tautology_del:                      0
% 3.14/0.96  sim_eq_tautology_del:                   202
% 3.14/0.96  sim_eq_res_simp:                        0
% 3.14/0.96  sim_fw_demodulated:                     4
% 3.14/0.96  sim_bw_demodulated:                     2
% 3.14/0.96  sim_light_normalised:                   29
% 3.14/0.96  sim_joinable_taut:                      0
% 3.14/0.96  sim_joinable_simp:                      0
% 3.14/0.96  sim_ac_normalised:                      0
% 3.14/0.96  sim_smt_subsumption:                    0
% 3.14/0.96  
%------------------------------------------------------------------------------
