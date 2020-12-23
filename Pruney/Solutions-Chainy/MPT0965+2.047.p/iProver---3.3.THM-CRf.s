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
% DateTime   : Thu Dec  3 12:00:29 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 326 expanded)
%              Number of clauses        :   63 ( 108 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   21
%              Number of atoms          :  405 (1444 expanded)
%              Number of equality atoms :  159 ( 394 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK7,sK6),sK5)
      & k1_xboole_0 != sK5
      & r2_hidden(sK6,sK4)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK6),sK5)
    & k1_xboole_0 != sK5
    & r2_hidden(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f40])).

fof(f66,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f21])).

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

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f71,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f64,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f67,plain,(
    r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ~ r2_hidden(k1_funct_1(sK7,sK6),sK5) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1150,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1154,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2060,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1150,c_1154])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X1
    | sK5 != X2
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_545,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_547,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_545,c_25,c_23])).

cnf(c_2061,plain,
    ( k1_relat_1(sK7) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2060,c_547])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_436,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1145,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_2382,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2061,c_1145])).

cnf(c_30,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1433,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_1434,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1433])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1448,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1449,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_2751,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2382,c_30,c_1434,c_1449])).

cnf(c_2752,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2751])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1153,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1626,plain,
    ( k2_relset_1(sK4,sK5,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1150,c_1153])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2239,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_1155])).

cnf(c_2681,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2239,c_30])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1159,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2687,plain,
    ( m1_subset_1(X0,sK5) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_1159])).

cnf(c_3094,plain,
    ( m1_subset_1(k1_funct_1(sK7,X0),sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2752,c_2687])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1160,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3659,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_1160])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1151,plain,
    ( r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1161,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1500,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1161])).

cnf(c_2021,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1500,c_30,c_1434,c_1449])).

cnf(c_2377,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2061,c_2021])).

cnf(c_2508,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_2377])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1162,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1158,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2688,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_1158])).

cnf(c_3324,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_2688])).

cnf(c_3926,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),sK5) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3659,c_2508,c_3324])).

cnf(c_3927,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_3926])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK7,sK6),sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1152,plain,
    ( r2_hidden(k1_funct_1(sK7,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3939,plain,
    ( r2_hidden(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3927,c_1152])).

cnf(c_31,plain,
    ( r2_hidden(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3939,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:26:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.21/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.01  
% 2.21/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/1.01  
% 2.21/1.01  ------  iProver source info
% 2.21/1.01  
% 2.21/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.21/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/1.01  git: non_committed_changes: false
% 2.21/1.01  git: last_make_outside_of_git: false
% 2.21/1.01  
% 2.21/1.01  ------ 
% 2.21/1.01  
% 2.21/1.01  ------ Input Options
% 2.21/1.01  
% 2.21/1.01  --out_options                           all
% 2.21/1.01  --tptp_safe_out                         true
% 2.21/1.01  --problem_path                          ""
% 2.21/1.01  --include_path                          ""
% 2.21/1.01  --clausifier                            res/vclausify_rel
% 2.21/1.01  --clausifier_options                    --mode clausify
% 2.21/1.01  --stdin                                 false
% 2.21/1.01  --stats_out                             all
% 2.21/1.01  
% 2.21/1.01  ------ General Options
% 2.21/1.01  
% 2.21/1.01  --fof                                   false
% 2.21/1.01  --time_out_real                         305.
% 2.21/1.01  --time_out_virtual                      -1.
% 2.21/1.01  --symbol_type_check                     false
% 2.21/1.01  --clausify_out                          false
% 2.21/1.01  --sig_cnt_out                           false
% 2.21/1.01  --trig_cnt_out                          false
% 2.21/1.01  --trig_cnt_out_tolerance                1.
% 2.21/1.01  --trig_cnt_out_sk_spl                   false
% 2.21/1.01  --abstr_cl_out                          false
% 2.21/1.01  
% 2.21/1.01  ------ Global Options
% 2.21/1.01  
% 2.21/1.01  --schedule                              default
% 2.21/1.01  --add_important_lit                     false
% 2.21/1.01  --prop_solver_per_cl                    1000
% 2.21/1.01  --min_unsat_core                        false
% 2.21/1.01  --soft_assumptions                      false
% 2.21/1.01  --soft_lemma_size                       3
% 2.21/1.01  --prop_impl_unit_size                   0
% 2.21/1.01  --prop_impl_unit                        []
% 2.21/1.01  --share_sel_clauses                     true
% 2.21/1.01  --reset_solvers                         false
% 2.21/1.01  --bc_imp_inh                            [conj_cone]
% 2.21/1.01  --conj_cone_tolerance                   3.
% 2.21/1.01  --extra_neg_conj                        none
% 2.21/1.01  --large_theory_mode                     true
% 2.21/1.01  --prolific_symb_bound                   200
% 2.21/1.01  --lt_threshold                          2000
% 2.21/1.01  --clause_weak_htbl                      true
% 2.21/1.01  --gc_record_bc_elim                     false
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing Options
% 2.21/1.01  
% 2.21/1.01  --preprocessing_flag                    true
% 2.21/1.01  --time_out_prep_mult                    0.1
% 2.21/1.01  --splitting_mode                        input
% 2.21/1.01  --splitting_grd                         true
% 2.21/1.01  --splitting_cvd                         false
% 2.21/1.01  --splitting_cvd_svl                     false
% 2.21/1.01  --splitting_nvd                         32
% 2.21/1.01  --sub_typing                            true
% 2.21/1.01  --prep_gs_sim                           true
% 2.21/1.01  --prep_unflatten                        true
% 2.21/1.01  --prep_res_sim                          true
% 2.21/1.01  --prep_upred                            true
% 2.21/1.01  --prep_sem_filter                       exhaustive
% 2.21/1.01  --prep_sem_filter_out                   false
% 2.21/1.01  --pred_elim                             true
% 2.21/1.01  --res_sim_input                         true
% 2.21/1.01  --eq_ax_congr_red                       true
% 2.21/1.01  --pure_diseq_elim                       true
% 2.21/1.01  --brand_transform                       false
% 2.21/1.01  --non_eq_to_eq                          false
% 2.21/1.01  --prep_def_merge                        true
% 2.21/1.01  --prep_def_merge_prop_impl              false
% 2.21/1.01  --prep_def_merge_mbd                    true
% 2.21/1.01  --prep_def_merge_tr_red                 false
% 2.21/1.01  --prep_def_merge_tr_cl                  false
% 2.21/1.01  --smt_preprocessing                     true
% 2.21/1.01  --smt_ac_axioms                         fast
% 2.21/1.01  --preprocessed_out                      false
% 2.21/1.01  --preprocessed_stats                    false
% 2.21/1.01  
% 2.21/1.01  ------ Abstraction refinement Options
% 2.21/1.01  
% 2.21/1.01  --abstr_ref                             []
% 2.21/1.01  --abstr_ref_prep                        false
% 2.21/1.01  --abstr_ref_until_sat                   false
% 2.21/1.01  --abstr_ref_sig_restrict                funpre
% 2.21/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.01  --abstr_ref_under                       []
% 2.21/1.01  
% 2.21/1.01  ------ SAT Options
% 2.21/1.01  
% 2.21/1.01  --sat_mode                              false
% 2.21/1.01  --sat_fm_restart_options                ""
% 2.21/1.01  --sat_gr_def                            false
% 2.21/1.01  --sat_epr_types                         true
% 2.21/1.01  --sat_non_cyclic_types                  false
% 2.21/1.01  --sat_finite_models                     false
% 2.21/1.01  --sat_fm_lemmas                         false
% 2.21/1.01  --sat_fm_prep                           false
% 2.21/1.01  --sat_fm_uc_incr                        true
% 2.21/1.01  --sat_out_model                         small
% 2.21/1.01  --sat_out_clauses                       false
% 2.21/1.01  
% 2.21/1.01  ------ QBF Options
% 2.21/1.01  
% 2.21/1.01  --qbf_mode                              false
% 2.21/1.01  --qbf_elim_univ                         false
% 2.21/1.01  --qbf_dom_inst                          none
% 2.21/1.01  --qbf_dom_pre_inst                      false
% 2.21/1.01  --qbf_sk_in                             false
% 2.21/1.01  --qbf_pred_elim                         true
% 2.21/1.01  --qbf_split                             512
% 2.21/1.01  
% 2.21/1.01  ------ BMC1 Options
% 2.21/1.01  
% 2.21/1.01  --bmc1_incremental                      false
% 2.21/1.01  --bmc1_axioms                           reachable_all
% 2.21/1.01  --bmc1_min_bound                        0
% 2.21/1.01  --bmc1_max_bound                        -1
% 2.21/1.01  --bmc1_max_bound_default                -1
% 2.21/1.01  --bmc1_symbol_reachability              true
% 2.21/1.01  --bmc1_property_lemmas                  false
% 2.21/1.01  --bmc1_k_induction                      false
% 2.21/1.01  --bmc1_non_equiv_states                 false
% 2.21/1.01  --bmc1_deadlock                         false
% 2.21/1.01  --bmc1_ucm                              false
% 2.21/1.01  --bmc1_add_unsat_core                   none
% 2.21/1.01  --bmc1_unsat_core_children              false
% 2.21/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.01  --bmc1_out_stat                         full
% 2.21/1.01  --bmc1_ground_init                      false
% 2.21/1.01  --bmc1_pre_inst_next_state              false
% 2.21/1.01  --bmc1_pre_inst_state                   false
% 2.21/1.01  --bmc1_pre_inst_reach_state             false
% 2.21/1.01  --bmc1_out_unsat_core                   false
% 2.21/1.01  --bmc1_aig_witness_out                  false
% 2.21/1.01  --bmc1_verbose                          false
% 2.21/1.01  --bmc1_dump_clauses_tptp                false
% 2.21/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.01  --bmc1_dump_file                        -
% 2.21/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.01  --bmc1_ucm_extend_mode                  1
% 2.21/1.01  --bmc1_ucm_init_mode                    2
% 2.21/1.01  --bmc1_ucm_cone_mode                    none
% 2.21/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.01  --bmc1_ucm_relax_model                  4
% 2.21/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.01  --bmc1_ucm_layered_model                none
% 2.21/1.01  --bmc1_ucm_max_lemma_size               10
% 2.21/1.01  
% 2.21/1.01  ------ AIG Options
% 2.21/1.01  
% 2.21/1.01  --aig_mode                              false
% 2.21/1.01  
% 2.21/1.01  ------ Instantiation Options
% 2.21/1.01  
% 2.21/1.01  --instantiation_flag                    true
% 2.21/1.01  --inst_sos_flag                         false
% 2.21/1.01  --inst_sos_phase                        true
% 2.21/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.01  --inst_lit_sel_side                     num_symb
% 2.21/1.01  --inst_solver_per_active                1400
% 2.21/1.01  --inst_solver_calls_frac                1.
% 2.21/1.01  --inst_passive_queue_type               priority_queues
% 2.21/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.01  --inst_passive_queues_freq              [25;2]
% 2.21/1.01  --inst_dismatching                      true
% 2.21/1.01  --inst_eager_unprocessed_to_passive     true
% 2.21/1.01  --inst_prop_sim_given                   true
% 2.21/1.01  --inst_prop_sim_new                     false
% 2.21/1.01  --inst_subs_new                         false
% 2.21/1.01  --inst_eq_res_simp                      false
% 2.21/1.01  --inst_subs_given                       false
% 2.21/1.01  --inst_orphan_elimination               true
% 2.21/1.01  --inst_learning_loop_flag               true
% 2.21/1.01  --inst_learning_start                   3000
% 2.21/1.01  --inst_learning_factor                  2
% 2.21/1.01  --inst_start_prop_sim_after_learn       3
% 2.21/1.01  --inst_sel_renew                        solver
% 2.21/1.01  --inst_lit_activity_flag                true
% 2.21/1.01  --inst_restr_to_given                   false
% 2.21/1.01  --inst_activity_threshold               500
% 2.21/1.01  --inst_out_proof                        true
% 2.21/1.01  
% 2.21/1.01  ------ Resolution Options
% 2.21/1.01  
% 2.21/1.01  --resolution_flag                       true
% 2.21/1.01  --res_lit_sel                           adaptive
% 2.21/1.01  --res_lit_sel_side                      none
% 2.21/1.01  --res_ordering                          kbo
% 2.21/1.01  --res_to_prop_solver                    active
% 2.21/1.01  --res_prop_simpl_new                    false
% 2.21/1.01  --res_prop_simpl_given                  true
% 2.21/1.01  --res_passive_queue_type                priority_queues
% 2.21/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.01  --res_passive_queues_freq               [15;5]
% 2.21/1.01  --res_forward_subs                      full
% 2.21/1.01  --res_backward_subs                     full
% 2.21/1.01  --res_forward_subs_resolution           true
% 2.21/1.01  --res_backward_subs_resolution          true
% 2.21/1.01  --res_orphan_elimination                true
% 2.21/1.01  --res_time_limit                        2.
% 2.21/1.01  --res_out_proof                         true
% 2.21/1.01  
% 2.21/1.01  ------ Superposition Options
% 2.21/1.01  
% 2.21/1.01  --superposition_flag                    true
% 2.21/1.01  --sup_passive_queue_type                priority_queues
% 2.21/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.01  --demod_completeness_check              fast
% 2.21/1.01  --demod_use_ground                      true
% 2.21/1.01  --sup_to_prop_solver                    passive
% 2.21/1.01  --sup_prop_simpl_new                    true
% 2.21/1.01  --sup_prop_simpl_given                  true
% 2.21/1.01  --sup_fun_splitting                     false
% 2.21/1.01  --sup_smt_interval                      50000
% 2.21/1.01  
% 2.21/1.01  ------ Superposition Simplification Setup
% 2.21/1.01  
% 2.21/1.01  --sup_indices_passive                   []
% 2.21/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_full_bw                           [BwDemod]
% 2.21/1.01  --sup_immed_triv                        [TrivRules]
% 2.21/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_immed_bw_main                     []
% 2.21/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.01  
% 2.21/1.01  ------ Combination Options
% 2.21/1.01  
% 2.21/1.01  --comb_res_mult                         3
% 2.21/1.01  --comb_sup_mult                         2
% 2.21/1.01  --comb_inst_mult                        10
% 2.21/1.01  
% 2.21/1.01  ------ Debug Options
% 2.21/1.01  
% 2.21/1.01  --dbg_backtrace                         false
% 2.21/1.01  --dbg_dump_prop_clauses                 false
% 2.21/1.01  --dbg_dump_prop_clauses_file            -
% 2.21/1.01  --dbg_out_stat                          false
% 2.21/1.01  ------ Parsing...
% 2.21/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/1.01  ------ Proving...
% 2.21/1.01  ------ Problem Properties 
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  clauses                                 23
% 2.21/1.01  conjectures                             4
% 2.21/1.01  EPR                                     4
% 2.21/1.01  Horn                                    18
% 2.21/1.01  unary                                   6
% 2.21/1.01  binary                                  5
% 2.21/1.01  lits                                    57
% 2.21/1.01  lits eq                                 15
% 2.21/1.01  fd_pure                                 0
% 2.21/1.01  fd_pseudo                               0
% 2.21/1.01  fd_cond                                 3
% 2.21/1.01  fd_pseudo_cond                          0
% 2.21/1.01  AC symbols                              0
% 2.21/1.01  
% 2.21/1.01  ------ Schedule dynamic 5 is on 
% 2.21/1.01  
% 2.21/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  ------ 
% 2.21/1.01  Current options:
% 2.21/1.01  ------ 
% 2.21/1.01  
% 2.21/1.01  ------ Input Options
% 2.21/1.01  
% 2.21/1.01  --out_options                           all
% 2.21/1.01  --tptp_safe_out                         true
% 2.21/1.01  --problem_path                          ""
% 2.21/1.01  --include_path                          ""
% 2.21/1.01  --clausifier                            res/vclausify_rel
% 2.21/1.01  --clausifier_options                    --mode clausify
% 2.21/1.01  --stdin                                 false
% 2.21/1.01  --stats_out                             all
% 2.21/1.01  
% 2.21/1.01  ------ General Options
% 2.21/1.01  
% 2.21/1.01  --fof                                   false
% 2.21/1.01  --time_out_real                         305.
% 2.21/1.01  --time_out_virtual                      -1.
% 2.21/1.01  --symbol_type_check                     false
% 2.21/1.01  --clausify_out                          false
% 2.21/1.01  --sig_cnt_out                           false
% 2.21/1.01  --trig_cnt_out                          false
% 2.21/1.01  --trig_cnt_out_tolerance                1.
% 2.21/1.01  --trig_cnt_out_sk_spl                   false
% 2.21/1.01  --abstr_cl_out                          false
% 2.21/1.01  
% 2.21/1.01  ------ Global Options
% 2.21/1.01  
% 2.21/1.01  --schedule                              default
% 2.21/1.01  --add_important_lit                     false
% 2.21/1.01  --prop_solver_per_cl                    1000
% 2.21/1.01  --min_unsat_core                        false
% 2.21/1.01  --soft_assumptions                      false
% 2.21/1.01  --soft_lemma_size                       3
% 2.21/1.01  --prop_impl_unit_size                   0
% 2.21/1.01  --prop_impl_unit                        []
% 2.21/1.01  --share_sel_clauses                     true
% 2.21/1.01  --reset_solvers                         false
% 2.21/1.01  --bc_imp_inh                            [conj_cone]
% 2.21/1.01  --conj_cone_tolerance                   3.
% 2.21/1.01  --extra_neg_conj                        none
% 2.21/1.01  --large_theory_mode                     true
% 2.21/1.01  --prolific_symb_bound                   200
% 2.21/1.01  --lt_threshold                          2000
% 2.21/1.01  --clause_weak_htbl                      true
% 2.21/1.01  --gc_record_bc_elim                     false
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing Options
% 2.21/1.01  
% 2.21/1.01  --preprocessing_flag                    true
% 2.21/1.01  --time_out_prep_mult                    0.1
% 2.21/1.01  --splitting_mode                        input
% 2.21/1.01  --splitting_grd                         true
% 2.21/1.01  --splitting_cvd                         false
% 2.21/1.01  --splitting_cvd_svl                     false
% 2.21/1.01  --splitting_nvd                         32
% 2.21/1.01  --sub_typing                            true
% 2.21/1.01  --prep_gs_sim                           true
% 2.21/1.01  --prep_unflatten                        true
% 2.21/1.01  --prep_res_sim                          true
% 2.21/1.01  --prep_upred                            true
% 2.21/1.01  --prep_sem_filter                       exhaustive
% 2.21/1.01  --prep_sem_filter_out                   false
% 2.21/1.01  --pred_elim                             true
% 2.21/1.01  --res_sim_input                         true
% 2.21/1.01  --eq_ax_congr_red                       true
% 2.21/1.01  --pure_diseq_elim                       true
% 2.21/1.01  --brand_transform                       false
% 2.21/1.01  --non_eq_to_eq                          false
% 2.21/1.01  --prep_def_merge                        true
% 2.21/1.01  --prep_def_merge_prop_impl              false
% 2.21/1.01  --prep_def_merge_mbd                    true
% 2.21/1.01  --prep_def_merge_tr_red                 false
% 2.21/1.01  --prep_def_merge_tr_cl                  false
% 2.21/1.01  --smt_preprocessing                     true
% 2.21/1.01  --smt_ac_axioms                         fast
% 2.21/1.01  --preprocessed_out                      false
% 2.21/1.01  --preprocessed_stats                    false
% 2.21/1.01  
% 2.21/1.01  ------ Abstraction refinement Options
% 2.21/1.01  
% 2.21/1.01  --abstr_ref                             []
% 2.21/1.01  --abstr_ref_prep                        false
% 2.21/1.01  --abstr_ref_until_sat                   false
% 2.21/1.01  --abstr_ref_sig_restrict                funpre
% 2.21/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.01  --abstr_ref_under                       []
% 2.21/1.01  
% 2.21/1.01  ------ SAT Options
% 2.21/1.01  
% 2.21/1.01  --sat_mode                              false
% 2.21/1.01  --sat_fm_restart_options                ""
% 2.21/1.01  --sat_gr_def                            false
% 2.21/1.01  --sat_epr_types                         true
% 2.21/1.01  --sat_non_cyclic_types                  false
% 2.21/1.01  --sat_finite_models                     false
% 2.21/1.01  --sat_fm_lemmas                         false
% 2.21/1.01  --sat_fm_prep                           false
% 2.21/1.01  --sat_fm_uc_incr                        true
% 2.21/1.01  --sat_out_model                         small
% 2.21/1.01  --sat_out_clauses                       false
% 2.21/1.01  
% 2.21/1.01  ------ QBF Options
% 2.21/1.01  
% 2.21/1.01  --qbf_mode                              false
% 2.21/1.01  --qbf_elim_univ                         false
% 2.21/1.01  --qbf_dom_inst                          none
% 2.21/1.01  --qbf_dom_pre_inst                      false
% 2.21/1.01  --qbf_sk_in                             false
% 2.21/1.01  --qbf_pred_elim                         true
% 2.21/1.01  --qbf_split                             512
% 2.21/1.01  
% 2.21/1.01  ------ BMC1 Options
% 2.21/1.01  
% 2.21/1.01  --bmc1_incremental                      false
% 2.21/1.01  --bmc1_axioms                           reachable_all
% 2.21/1.01  --bmc1_min_bound                        0
% 2.21/1.01  --bmc1_max_bound                        -1
% 2.21/1.01  --bmc1_max_bound_default                -1
% 2.21/1.01  --bmc1_symbol_reachability              true
% 2.21/1.01  --bmc1_property_lemmas                  false
% 2.21/1.01  --bmc1_k_induction                      false
% 2.21/1.01  --bmc1_non_equiv_states                 false
% 2.21/1.01  --bmc1_deadlock                         false
% 2.21/1.01  --bmc1_ucm                              false
% 2.21/1.01  --bmc1_add_unsat_core                   none
% 2.21/1.01  --bmc1_unsat_core_children              false
% 2.21/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.01  --bmc1_out_stat                         full
% 2.21/1.01  --bmc1_ground_init                      false
% 2.21/1.01  --bmc1_pre_inst_next_state              false
% 2.21/1.01  --bmc1_pre_inst_state                   false
% 2.21/1.01  --bmc1_pre_inst_reach_state             false
% 2.21/1.01  --bmc1_out_unsat_core                   false
% 2.21/1.01  --bmc1_aig_witness_out                  false
% 2.21/1.01  --bmc1_verbose                          false
% 2.21/1.01  --bmc1_dump_clauses_tptp                false
% 2.21/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.01  --bmc1_dump_file                        -
% 2.21/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.01  --bmc1_ucm_extend_mode                  1
% 2.21/1.01  --bmc1_ucm_init_mode                    2
% 2.21/1.01  --bmc1_ucm_cone_mode                    none
% 2.21/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.01  --bmc1_ucm_relax_model                  4
% 2.21/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.01  --bmc1_ucm_layered_model                none
% 2.21/1.01  --bmc1_ucm_max_lemma_size               10
% 2.21/1.01  
% 2.21/1.01  ------ AIG Options
% 2.21/1.01  
% 2.21/1.01  --aig_mode                              false
% 2.21/1.01  
% 2.21/1.01  ------ Instantiation Options
% 2.21/1.01  
% 2.21/1.01  --instantiation_flag                    true
% 2.21/1.01  --inst_sos_flag                         false
% 2.21/1.01  --inst_sos_phase                        true
% 2.21/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.01  --inst_lit_sel_side                     none
% 2.21/1.01  --inst_solver_per_active                1400
% 2.21/1.01  --inst_solver_calls_frac                1.
% 2.21/1.01  --inst_passive_queue_type               priority_queues
% 2.21/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.01  --inst_passive_queues_freq              [25;2]
% 2.21/1.01  --inst_dismatching                      true
% 2.21/1.01  --inst_eager_unprocessed_to_passive     true
% 2.21/1.01  --inst_prop_sim_given                   true
% 2.21/1.01  --inst_prop_sim_new                     false
% 2.21/1.01  --inst_subs_new                         false
% 2.21/1.01  --inst_eq_res_simp                      false
% 2.21/1.01  --inst_subs_given                       false
% 2.21/1.01  --inst_orphan_elimination               true
% 2.21/1.01  --inst_learning_loop_flag               true
% 2.21/1.01  --inst_learning_start                   3000
% 2.21/1.01  --inst_learning_factor                  2
% 2.21/1.01  --inst_start_prop_sim_after_learn       3
% 2.21/1.01  --inst_sel_renew                        solver
% 2.21/1.01  --inst_lit_activity_flag                true
% 2.21/1.01  --inst_restr_to_given                   false
% 2.21/1.01  --inst_activity_threshold               500
% 2.21/1.01  --inst_out_proof                        true
% 2.21/1.01  
% 2.21/1.01  ------ Resolution Options
% 2.21/1.01  
% 2.21/1.01  --resolution_flag                       false
% 2.21/1.01  --res_lit_sel                           adaptive
% 2.21/1.01  --res_lit_sel_side                      none
% 2.21/1.01  --res_ordering                          kbo
% 2.21/1.01  --res_to_prop_solver                    active
% 2.21/1.01  --res_prop_simpl_new                    false
% 2.21/1.01  --res_prop_simpl_given                  true
% 2.21/1.01  --res_passive_queue_type                priority_queues
% 2.21/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.01  --res_passive_queues_freq               [15;5]
% 2.21/1.01  --res_forward_subs                      full
% 2.21/1.01  --res_backward_subs                     full
% 2.21/1.01  --res_forward_subs_resolution           true
% 2.21/1.01  --res_backward_subs_resolution          true
% 2.21/1.01  --res_orphan_elimination                true
% 2.21/1.01  --res_time_limit                        2.
% 2.21/1.01  --res_out_proof                         true
% 2.21/1.01  
% 2.21/1.01  ------ Superposition Options
% 2.21/1.01  
% 2.21/1.01  --superposition_flag                    true
% 2.21/1.01  --sup_passive_queue_type                priority_queues
% 2.21/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.01  --demod_completeness_check              fast
% 2.21/1.01  --demod_use_ground                      true
% 2.21/1.01  --sup_to_prop_solver                    passive
% 2.21/1.01  --sup_prop_simpl_new                    true
% 2.21/1.01  --sup_prop_simpl_given                  true
% 2.21/1.01  --sup_fun_splitting                     false
% 2.21/1.01  --sup_smt_interval                      50000
% 2.21/1.01  
% 2.21/1.01  ------ Superposition Simplification Setup
% 2.21/1.01  
% 2.21/1.01  --sup_indices_passive                   []
% 2.21/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_full_bw                           [BwDemod]
% 2.21/1.01  --sup_immed_triv                        [TrivRules]
% 2.21/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_immed_bw_main                     []
% 2.21/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.01  
% 2.21/1.01  ------ Combination Options
% 2.21/1.01  
% 2.21/1.01  --comb_res_mult                         3
% 2.21/1.01  --comb_sup_mult                         2
% 2.21/1.01  --comb_inst_mult                        10
% 2.21/1.01  
% 2.21/1.01  ------ Debug Options
% 2.21/1.01  
% 2.21/1.01  --dbg_backtrace                         false
% 2.21/1.01  --dbg_dump_prop_clauses                 false
% 2.21/1.01  --dbg_dump_prop_clauses_file            -
% 2.21/1.01  --dbg_out_stat                          false
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  ------ Proving...
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  % SZS status Theorem for theBenchmark.p
% 2.21/1.01  
% 2.21/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/1.01  
% 2.21/1.01  fof(f12,conjecture,(
% 2.21/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f13,negated_conjecture,(
% 2.21/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.21/1.01    inference(negated_conjecture,[],[f12])).
% 2.21/1.01  
% 2.21/1.01  fof(f27,plain,(
% 2.21/1.01    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.21/1.01    inference(ennf_transformation,[],[f13])).
% 2.21/1.01  
% 2.21/1.01  fof(f28,plain,(
% 2.21/1.01    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.21/1.01    inference(flattening,[],[f27])).
% 2.21/1.01  
% 2.21/1.01  fof(f40,plain,(
% 2.21/1.01    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK7,sK6),sK5) & k1_xboole_0 != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 2.21/1.01    introduced(choice_axiom,[])).
% 2.21/1.01  
% 2.21/1.01  fof(f41,plain,(
% 2.21/1.01    ~r2_hidden(k1_funct_1(sK7,sK6),sK5) & k1_xboole_0 != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 2.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f40])).
% 2.21/1.01  
% 2.21/1.01  fof(f66,plain,(
% 2.21/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.21/1.01    inference(cnf_transformation,[],[f41])).
% 2.21/1.01  
% 2.21/1.01  fof(f9,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f23,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f9])).
% 2.21/1.01  
% 2.21/1.01  fof(f56,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f23])).
% 2.21/1.01  
% 2.21/1.01  fof(f11,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f25,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f11])).
% 2.21/1.01  
% 2.21/1.01  fof(f26,plain,(
% 2.21/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(flattening,[],[f25])).
% 2.21/1.01  
% 2.21/1.01  fof(f39,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(nnf_transformation,[],[f26])).
% 2.21/1.01  
% 2.21/1.01  fof(f58,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f39])).
% 2.21/1.01  
% 2.21/1.01  fof(f65,plain,(
% 2.21/1.01    v1_funct_2(sK7,sK4,sK5)),
% 2.21/1.01    inference(cnf_transformation,[],[f41])).
% 2.21/1.01  
% 2.21/1.01  fof(f68,plain,(
% 2.21/1.01    k1_xboole_0 != sK5),
% 2.21/1.01    inference(cnf_transformation,[],[f41])).
% 2.21/1.01  
% 2.21/1.01  fof(f7,axiom,(
% 2.21/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f20,plain,(
% 2.21/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/1.01    inference(ennf_transformation,[],[f7])).
% 2.21/1.01  
% 2.21/1.01  fof(f21,plain,(
% 2.21/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.01    inference(flattening,[],[f20])).
% 2.21/1.01  
% 2.21/1.01  fof(f33,plain,(
% 2.21/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.01    inference(nnf_transformation,[],[f21])).
% 2.21/1.01  
% 2.21/1.01  fof(f34,plain,(
% 2.21/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.01    inference(rectify,[],[f33])).
% 2.21/1.01  
% 2.21/1.01  fof(f37,plain,(
% 2.21/1.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 2.21/1.01    introduced(choice_axiom,[])).
% 2.21/1.01  
% 2.21/1.01  fof(f36,plain,(
% 2.21/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 2.21/1.01    introduced(choice_axiom,[])).
% 2.21/1.01  
% 2.21/1.01  fof(f35,plain,(
% 2.21/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 2.21/1.01    introduced(choice_axiom,[])).
% 2.21/1.01  
% 2.21/1.01  fof(f38,plain,(
% 2.21/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 2.21/1.01  
% 2.21/1.01  fof(f51,plain,(
% 2.21/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f38])).
% 2.21/1.01  
% 2.21/1.01  fof(f70,plain,(
% 2.21/1.01    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/1.01    inference(equality_resolution,[],[f51])).
% 2.21/1.01  
% 2.21/1.01  fof(f71,plain,(
% 2.21/1.01    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/1.01    inference(equality_resolution,[],[f70])).
% 2.21/1.01  
% 2.21/1.01  fof(f64,plain,(
% 2.21/1.01    v1_funct_1(sK7)),
% 2.21/1.01    inference(cnf_transformation,[],[f41])).
% 2.21/1.01  
% 2.21/1.01  fof(f5,axiom,(
% 2.21/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f19,plain,(
% 2.21/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.21/1.01    inference(ennf_transformation,[],[f5])).
% 2.21/1.01  
% 2.21/1.01  fof(f47,plain,(
% 2.21/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f19])).
% 2.21/1.01  
% 2.21/1.01  fof(f6,axiom,(
% 2.21/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f48,plain,(
% 2.21/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f6])).
% 2.21/1.01  
% 2.21/1.01  fof(f10,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f24,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f10])).
% 2.21/1.01  
% 2.21/1.01  fof(f57,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f24])).
% 2.21/1.01  
% 2.21/1.01  fof(f8,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f22,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.01    inference(ennf_transformation,[],[f8])).
% 2.21/1.01  
% 2.21/1.01  fof(f55,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.01    inference(cnf_transformation,[],[f22])).
% 2.21/1.01  
% 2.21/1.01  fof(f3,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f16,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.21/1.01    inference(ennf_transformation,[],[f3])).
% 2.21/1.01  
% 2.21/1.01  fof(f17,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.21/1.01    inference(flattening,[],[f16])).
% 2.21/1.01  
% 2.21/1.01  fof(f45,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f17])).
% 2.21/1.01  
% 2.21/1.01  fof(f2,axiom,(
% 2.21/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f14,plain,(
% 2.21/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.21/1.01    inference(ennf_transformation,[],[f2])).
% 2.21/1.01  
% 2.21/1.01  fof(f15,plain,(
% 2.21/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.21/1.01    inference(flattening,[],[f14])).
% 2.21/1.01  
% 2.21/1.01  fof(f44,plain,(
% 2.21/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f15])).
% 2.21/1.01  
% 2.21/1.01  fof(f67,plain,(
% 2.21/1.01    r2_hidden(sK6,sK4)),
% 2.21/1.01    inference(cnf_transformation,[],[f41])).
% 2.21/1.01  
% 2.21/1.01  fof(f1,axiom,(
% 2.21/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f29,plain,(
% 2.21/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.21/1.01    inference(nnf_transformation,[],[f1])).
% 2.21/1.01  
% 2.21/1.01  fof(f30,plain,(
% 2.21/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.21/1.01    inference(rectify,[],[f29])).
% 2.21/1.01  
% 2.21/1.01  fof(f31,plain,(
% 2.21/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.21/1.01    introduced(choice_axiom,[])).
% 2.21/1.01  
% 2.21/1.01  fof(f32,plain,(
% 2.21/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.21/1.01  
% 2.21/1.01  fof(f42,plain,(
% 2.21/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f32])).
% 2.21/1.01  
% 2.21/1.01  fof(f43,plain,(
% 2.21/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f32])).
% 2.21/1.01  
% 2.21/1.01  fof(f4,axiom,(
% 2.21/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.01  
% 2.21/1.01  fof(f18,plain,(
% 2.21/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.21/1.01    inference(ennf_transformation,[],[f4])).
% 2.21/1.01  
% 2.21/1.01  fof(f46,plain,(
% 2.21/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.21/1.01    inference(cnf_transformation,[],[f18])).
% 2.21/1.01  
% 2.21/1.01  fof(f69,plain,(
% 2.21/1.01    ~r2_hidden(k1_funct_1(sK7,sK6),sK5)),
% 2.21/1.01    inference(cnf_transformation,[],[f41])).
% 2.21/1.01  
% 2.21/1.01  cnf(c_25,negated_conjecture,
% 2.21/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 2.21/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1150,plain,
% 2.21/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_14,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1154,plain,
% 2.21/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.21/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2060,plain,
% 2.21/1.01      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1150,c_1154]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_21,plain,
% 2.21/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.21/1.01      | k1_xboole_0 = X2 ),
% 2.21/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_26,negated_conjecture,
% 2.21/1.01      ( v1_funct_2(sK7,sK4,sK5) ),
% 2.21/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_544,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.21/1.01      | sK4 != X1
% 2.21/1.01      | sK5 != X2
% 2.21/1.01      | sK7 != X0
% 2.21/1.01      | k1_xboole_0 = X2 ),
% 2.21/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_545,plain,
% 2.21/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.21/1.01      | k1_relset_1(sK4,sK5,sK7) = sK4
% 2.21/1.01      | k1_xboole_0 = sK5 ),
% 2.21/1.01      inference(unflattening,[status(thm)],[c_544]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_23,negated_conjecture,
% 2.21/1.01      ( k1_xboole_0 != sK5 ),
% 2.21/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_547,plain,
% 2.21/1.01      ( k1_relset_1(sK4,sK5,sK7) = sK4 ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_545,c_25,c_23]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2061,plain,
% 2.21/1.01      ( k1_relat_1(sK7) = sK4 ),
% 2.21/1.01      inference(light_normalisation,[status(thm)],[c_2060,c_547]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_10,plain,
% 2.21/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.21/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.21/1.01      | ~ v1_funct_1(X1)
% 2.21/1.01      | ~ v1_relat_1(X1) ),
% 2.21/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_27,negated_conjecture,
% 2.21/1.01      ( v1_funct_1(sK7) ),
% 2.21/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_435,plain,
% 2.21/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.21/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.21/1.01      | ~ v1_relat_1(X1)
% 2.21/1.01      | sK7 != X1 ),
% 2.21/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_436,plain,
% 2.21/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 2.21/1.01      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 2.21/1.01      | ~ v1_relat_1(sK7) ),
% 2.21/1.01      inference(unflattening,[status(thm)],[c_435]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1145,plain,
% 2.21/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.21/1.01      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 2.21/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2382,plain,
% 2.21/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.21/1.01      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 2.21/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.21/1.01      inference(demodulation,[status(thm)],[c_2061,c_1145]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_30,plain,
% 2.21/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_5,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.21/1.01      | ~ v1_relat_1(X1)
% 2.21/1.01      | v1_relat_1(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1328,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | v1_relat_1(X0)
% 2.21/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1433,plain,
% 2.21/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 2.21/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 2.21/1.01      | v1_relat_1(sK7) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_1328]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1434,plain,
% 2.21/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 2.21/1.01      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.21/1.01      | v1_relat_1(sK7) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1433]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_6,plain,
% 2.21/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.21/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1448,plain,
% 2.21/1.01      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 2.21/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1449,plain,
% 2.21/1.01      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1448]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2751,plain,
% 2.21/1.01      ( r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 2.21/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_2382,c_30,c_1434,c_1449]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2752,plain,
% 2.21/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.21/1.01      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top ),
% 2.21/1.01      inference(renaming,[status(thm)],[c_2751]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_15,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1153,plain,
% 2.21/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.21/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1626,plain,
% 2.21/1.01      ( k2_relset_1(sK4,sK5,sK7) = k2_relat_1(sK7) ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1150,c_1153]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_13,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.21/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1155,plain,
% 2.21/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.21/1.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2239,plain,
% 2.21/1.01      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5)) = iProver_top
% 2.21/1.01      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1626,c_1155]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2681,plain,
% 2.21/1.01      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK5)) = iProver_top ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_2239,c_30]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3,plain,
% 2.21/1.01      ( m1_subset_1(X0,X1)
% 2.21/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.21/1.01      | ~ r2_hidden(X0,X2) ),
% 2.21/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1159,plain,
% 2.21/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.21/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.21/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2687,plain,
% 2.21/1.01      ( m1_subset_1(X0,sK5) = iProver_top
% 2.21/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_2681,c_1159]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3094,plain,
% 2.21/1.01      ( m1_subset_1(k1_funct_1(sK7,X0),sK5) = iProver_top
% 2.21/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_2752,c_2687]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.21/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1160,plain,
% 2.21/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.21/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.21/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3659,plain,
% 2.21/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.21/1.01      | r2_hidden(k1_funct_1(sK7,X0),sK5) = iProver_top
% 2.21/1.01      | v1_xboole_0(sK5) = iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_3094,c_1160]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_24,negated_conjecture,
% 2.21/1.01      ( r2_hidden(sK6,sK4) ),
% 2.21/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1151,plain,
% 2.21/1.01      ( r2_hidden(sK6,sK4) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1,plain,
% 2.21/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.21/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1161,plain,
% 2.21/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.21/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1500,plain,
% 2.21/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.21/1.01      | v1_relat_1(sK7) != iProver_top
% 2.21/1.01      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1145,c_1161]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2021,plain,
% 2.21/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.21/1.01      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_1500,c_30,c_1434,c_1449]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2377,plain,
% 2.21/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.21/1.01      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 2.21/1.01      inference(demodulation,[status(thm)],[c_2061,c_2021]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2508,plain,
% 2.21/1.01      ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1151,c_2377]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_0,plain,
% 2.21/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.21/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1162,plain,
% 2.21/1.01      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.21/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_4,plain,
% 2.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.21/1.01      | ~ r2_hidden(X2,X0)
% 2.21/1.01      | ~ v1_xboole_0(X1) ),
% 2.21/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1158,plain,
% 2.21/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.21/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.21/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_2688,plain,
% 2.21/1.01      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 2.21/1.01      | v1_xboole_0(sK5) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_2681,c_1158]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3324,plain,
% 2.21/1.01      ( v1_xboole_0(k2_relat_1(sK7)) = iProver_top
% 2.21/1.01      | v1_xboole_0(sK5) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_1162,c_2688]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3926,plain,
% 2.21/1.01      ( r2_hidden(k1_funct_1(sK7,X0),sK5) = iProver_top
% 2.21/1.01      | r2_hidden(X0,sK4) != iProver_top ),
% 2.21/1.01      inference(global_propositional_subsumption,
% 2.21/1.01                [status(thm)],
% 2.21/1.01                [c_3659,c_2508,c_3324]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3927,plain,
% 2.21/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.21/1.01      | r2_hidden(k1_funct_1(sK7,X0),sK5) = iProver_top ),
% 2.21/1.01      inference(renaming,[status(thm)],[c_3926]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_22,negated_conjecture,
% 2.21/1.01      ( ~ r2_hidden(k1_funct_1(sK7,sK6),sK5) ),
% 2.21/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_1152,plain,
% 2.21/1.01      ( r2_hidden(k1_funct_1(sK7,sK6),sK5) != iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_3939,plain,
% 2.21/1.01      ( r2_hidden(sK6,sK4) != iProver_top ),
% 2.21/1.01      inference(superposition,[status(thm)],[c_3927,c_1152]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(c_31,plain,
% 2.21/1.01      ( r2_hidden(sK6,sK4) = iProver_top ),
% 2.21/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.21/1.01  
% 2.21/1.01  cnf(contradiction,plain,
% 2.21/1.01      ( $false ),
% 2.21/1.01      inference(minisat,[status(thm)],[c_3939,c_31]) ).
% 2.21/1.01  
% 2.21/1.01  
% 2.21/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/1.01  
% 2.21/1.01  ------                               Statistics
% 2.21/1.01  
% 2.21/1.01  ------ General
% 2.21/1.01  
% 2.21/1.01  abstr_ref_over_cycles:                  0
% 2.21/1.01  abstr_ref_under_cycles:                 0
% 2.21/1.01  gc_basic_clause_elim:                   0
% 2.21/1.01  forced_gc_time:                         0
% 2.21/1.01  parsing_time:                           0.011
% 2.21/1.01  unif_index_cands_time:                  0.
% 2.21/1.01  unif_index_add_time:                    0.
% 2.21/1.01  orderings_time:                         0.
% 2.21/1.01  out_proof_time:                         0.01
% 2.21/1.01  total_time:                             0.183
% 2.21/1.01  num_of_symbols:                         53
% 2.21/1.01  num_of_terms:                           2628
% 2.21/1.01  
% 2.21/1.01  ------ Preprocessing
% 2.21/1.01  
% 2.21/1.01  num_of_splits:                          0
% 2.21/1.01  num_of_split_atoms:                     0
% 2.21/1.01  num_of_reused_defs:                     0
% 2.21/1.01  num_eq_ax_congr_red:                    31
% 2.21/1.01  num_of_sem_filtered_clauses:            1
% 2.21/1.01  num_of_subtypes:                        0
% 2.21/1.01  monotx_restored_types:                  0
% 2.21/1.01  sat_num_of_epr_types:                   0
% 2.21/1.01  sat_num_of_non_cyclic_types:            0
% 2.21/1.01  sat_guarded_non_collapsed_types:        0
% 2.21/1.01  num_pure_diseq_elim:                    0
% 2.21/1.01  simp_replaced_by:                       0
% 2.21/1.01  res_preprocessed:                       126
% 2.21/1.01  prep_upred:                             0
% 2.21/1.01  prep_unflattend:                        37
% 2.21/1.01  smt_new_axioms:                         0
% 2.21/1.01  pred_elim_cands:                        4
% 2.21/1.01  pred_elim:                              2
% 2.21/1.01  pred_elim_cl:                           5
% 2.21/1.01  pred_elim_cycles:                       5
% 2.21/1.01  merged_defs:                            0
% 2.21/1.01  merged_defs_ncl:                        0
% 2.21/1.01  bin_hyper_res:                          0
% 2.21/1.01  prep_cycles:                            4
% 2.21/1.01  pred_elim_time:                         0.006
% 2.21/1.01  splitting_time:                         0.
% 2.21/1.01  sem_filter_time:                        0.
% 2.21/1.01  monotx_time:                            0.
% 2.21/1.01  subtype_inf_time:                       0.
% 2.21/1.01  
% 2.21/1.01  ------ Problem properties
% 2.21/1.01  
% 2.21/1.01  clauses:                                23
% 2.21/1.01  conjectures:                            4
% 2.21/1.01  epr:                                    4
% 2.21/1.01  horn:                                   18
% 2.21/1.01  ground:                                 7
% 2.21/1.01  unary:                                  6
% 2.21/1.01  binary:                                 5
% 2.21/1.01  lits:                                   57
% 2.21/1.01  lits_eq:                                15
% 2.21/1.01  fd_pure:                                0
% 2.21/1.01  fd_pseudo:                              0
% 2.21/1.01  fd_cond:                                3
% 2.21/1.01  fd_pseudo_cond:                         0
% 2.21/1.01  ac_symbols:                             0
% 2.21/1.01  
% 2.21/1.01  ------ Propositional Solver
% 2.21/1.01  
% 2.21/1.01  prop_solver_calls:                      30
% 2.21/1.01  prop_fast_solver_calls:                 911
% 2.21/1.01  smt_solver_calls:                       0
% 2.21/1.01  smt_fast_solver_calls:                  0
% 2.21/1.01  prop_num_of_clauses:                    1327
% 2.21/1.01  prop_preprocess_simplified:             4556
% 2.21/1.01  prop_fo_subsumed:                       31
% 2.21/1.01  prop_solver_time:                       0.
% 2.21/1.01  smt_solver_time:                        0.
% 2.21/1.01  smt_fast_solver_time:                   0.
% 2.21/1.01  prop_fast_solver_time:                  0.
% 2.21/1.01  prop_unsat_core_time:                   0.
% 2.21/1.01  
% 2.21/1.01  ------ QBF
% 2.21/1.01  
% 2.21/1.01  qbf_q_res:                              0
% 2.21/1.01  qbf_num_tautologies:                    0
% 2.21/1.01  qbf_prep_cycles:                        0
% 2.21/1.01  
% 2.21/1.01  ------ BMC1
% 2.21/1.01  
% 2.21/1.01  bmc1_current_bound:                     -1
% 2.21/1.01  bmc1_last_solved_bound:                 -1
% 2.21/1.01  bmc1_unsat_core_size:                   -1
% 2.21/1.01  bmc1_unsat_core_parents_size:           -1
% 2.21/1.01  bmc1_merge_next_fun:                    0
% 2.21/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.21/1.01  
% 2.21/1.01  ------ Instantiation
% 2.21/1.01  
% 2.21/1.01  inst_num_of_clauses:                    382
% 2.21/1.01  inst_num_in_passive:                    69
% 2.21/1.01  inst_num_in_active:                     249
% 2.21/1.01  inst_num_in_unprocessed:                64
% 2.21/1.01  inst_num_of_loops:                      320
% 2.21/1.01  inst_num_of_learning_restarts:          0
% 2.21/1.01  inst_num_moves_active_passive:          66
% 2.21/1.01  inst_lit_activity:                      0
% 2.21/1.01  inst_lit_activity_moves:                0
% 2.21/1.01  inst_num_tautologies:                   0
% 2.21/1.01  inst_num_prop_implied:                  0
% 2.21/1.01  inst_num_existing_simplified:           0
% 2.21/1.01  inst_num_eq_res_simplified:             0
% 2.21/1.02  inst_num_child_elim:                    0
% 2.21/1.02  inst_num_of_dismatching_blockings:      54
% 2.21/1.02  inst_num_of_non_proper_insts:           414
% 2.21/1.02  inst_num_of_duplicates:                 0
% 2.21/1.02  inst_inst_num_from_inst_to_res:         0
% 2.21/1.02  inst_dismatching_checking_time:         0.
% 2.21/1.02  
% 2.21/1.02  ------ Resolution
% 2.21/1.02  
% 2.21/1.02  res_num_of_clauses:                     0
% 2.21/1.02  res_num_in_passive:                     0
% 2.21/1.02  res_num_in_active:                      0
% 2.21/1.02  res_num_of_loops:                       130
% 2.21/1.02  res_forward_subset_subsumed:            38
% 2.21/1.02  res_backward_subset_subsumed:           0
% 2.21/1.02  res_forward_subsumed:                   0
% 2.21/1.02  res_backward_subsumed:                  0
% 2.21/1.02  res_forward_subsumption_resolution:     0
% 2.21/1.02  res_backward_subsumption_resolution:    0
% 2.21/1.02  res_clause_to_clause_subsumption:       170
% 2.21/1.02  res_orphan_elimination:                 0
% 2.21/1.02  res_tautology_del:                      44
% 2.21/1.02  res_num_eq_res_simplified:              0
% 2.21/1.02  res_num_sel_changes:                    0
% 2.21/1.02  res_moves_from_active_to_pass:          0
% 2.21/1.02  
% 2.21/1.02  ------ Superposition
% 2.21/1.02  
% 2.21/1.02  sup_time_total:                         0.
% 2.21/1.02  sup_time_generating:                    0.
% 2.21/1.02  sup_time_sim_full:                      0.
% 2.21/1.02  sup_time_sim_immed:                     0.
% 2.21/1.02  
% 2.21/1.02  sup_num_of_clauses:                     80
% 2.21/1.02  sup_num_in_active:                      56
% 2.21/1.02  sup_num_in_passive:                     24
% 2.21/1.02  sup_num_of_loops:                       62
% 2.21/1.02  sup_fw_superposition:                   51
% 2.21/1.02  sup_bw_superposition:                   44
% 2.21/1.02  sup_immediate_simplified:               15
% 2.21/1.02  sup_given_eliminated:                   1
% 2.21/1.02  comparisons_done:                       0
% 2.21/1.02  comparisons_avoided:                    10
% 2.21/1.02  
% 2.21/1.02  ------ Simplifications
% 2.21/1.02  
% 2.21/1.02  
% 2.21/1.02  sim_fw_subset_subsumed:                 9
% 2.21/1.02  sim_bw_subset_subsumed:                 0
% 2.21/1.02  sim_fw_subsumed:                        3
% 2.21/1.02  sim_bw_subsumed:                        2
% 2.21/1.02  sim_fw_subsumption_res:                 1
% 2.21/1.02  sim_bw_subsumption_res:                 0
% 2.21/1.02  sim_tautology_del:                      7
% 2.21/1.02  sim_eq_tautology_del:                   9
% 2.21/1.02  sim_eq_res_simp:                        0
% 2.21/1.02  sim_fw_demodulated:                     0
% 2.21/1.02  sim_bw_demodulated:                     6
% 2.21/1.02  sim_light_normalised:                   5
% 2.21/1.02  sim_joinable_taut:                      0
% 2.21/1.02  sim_joinable_simp:                      0
% 2.21/1.02  sim_ac_normalised:                      0
% 2.21/1.02  sim_smt_subsumption:                    0
% 2.21/1.02  
%------------------------------------------------------------------------------
