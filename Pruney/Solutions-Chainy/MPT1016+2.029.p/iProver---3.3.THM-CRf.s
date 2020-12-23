%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:57 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  192 (9227 expanded)
%              Number of clauses        :  134 (2618 expanded)
%              Number of leaves         :   17 (1853 expanded)
%              Depth                    :   29
%              Number of atoms          :  687 (67447 expanded)
%              Number of equality atoms :  315 (21553 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK4 != sK5
        & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5)
        & r2_hidden(sK5,X0)
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f35,f34])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f44,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_369,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_370,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_2711,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_371,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2934,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3043,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2934])).

cnf(c_3044,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3043])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3077,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3078,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3077])).

cnf(c_3473,plain,
    ( v2_funct_1(sK3) = iProver_top
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2711,c_25,c_371,c_3044,c_3078])).

cnf(c_3474,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3473])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_255,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_259,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_22,c_20])).

cnf(c_2260,plain,
    ( ~ v2_funct_1(sK3)
    | sP3_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_259])).

cnf(c_2720,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP3_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2260])).

cnf(c_3899,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0
    | sP3_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_3474,c_2720])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2724,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2259,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_259])).

cnf(c_2721,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2259])).

cnf(c_3355,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2724,c_2721])).

cnf(c_3479,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3474,c_3355])).

cnf(c_4458,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3899,c_3479])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_382,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_383,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_15,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_541,plain,
    ( ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_383,c_15])).

cnf(c_666,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_370,c_15])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_356,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_357,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_791,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_357,c_15])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_343,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_344,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_916,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_344,c_15])).

cnf(c_2271,plain,
    ( X0 != X1
    | sK1(X0) = sK1(X1) ),
    theory(equality)).

cnf(c_2283,plain,
    ( sK1(sK3) = sK1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_2262,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2289,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2262])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_2254,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_320])).

cnf(c_2263,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3195,plain,
    ( sK1(sK3) != X0
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_2263])).

cnf(c_3413,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_3195])).

cnf(c_2713,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_23,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_51,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_53,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_4087,plain,
    ( v2_funct_1(sK3) = iProver_top
    | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2713,c_23,c_25,c_53,c_3044,c_3078])).

cnf(c_4088,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4087])).

cnf(c_2722,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2728,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3156,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2722,c_2728])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2729,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3597,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3156,c_2729])).

cnf(c_4239,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3597,c_25])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2732,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4244,plain,
    ( m1_subset_1(X0,sK2) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_2732])).

cnf(c_4824,plain,
    ( m1_subset_1(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_4244])).

cnf(c_57,plain,
    ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_59,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_60,plain,
    ( sK1(X0) != sK0(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_62,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3192,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3193,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3192])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2734,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4245,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4239,c_2734])).

cnf(c_4903,plain,
    ( r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_4245])).

cnf(c_2712,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_54,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_56,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_3995,plain,
    ( v2_funct_1(sK3) = iProver_top
    | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2712,c_23,c_25,c_56,c_3044,c_3078])).

cnf(c_3996,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3995])).

cnf(c_4904,plain,
    ( r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3996,c_4245])).

cnf(c_5120,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4824,c_23,c_25,c_59,c_62,c_3044,c_3078,c_3193,c_4903,c_4904])).

cnf(c_5122,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5120])).

cnf(c_2253,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_320])).

cnf(c_5364,plain,
    ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
    | sK0(sK3) = sK1(X0) ),
    inference(instantiation,[status(thm)],[c_2253])).

cnf(c_5366,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK0(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_5364])).

cnf(c_5125,plain,
    ( sK2 = k1_xboole_0
    | sP3_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_5120,c_2720])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2725,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3354,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2725,c_2721])).

cnf(c_5127,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5120,c_3354])).

cnf(c_16,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2726,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5131,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_5120,c_2726])).

cnf(c_5144,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP3_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5127,c_5131])).

cnf(c_5647,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5125,c_5144])).

cnf(c_5126,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_5120,c_3355])).

cnf(c_5648,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5125,c_5126])).

cnf(c_6570,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_5647,c_5648])).

cnf(c_6572,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4458,c_20,c_541,c_666,c_791,c_916,c_2283,c_2289,c_2254,c_3043,c_3077,c_3413,c_5122,c_5366,c_6570])).

cnf(c_6587,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6572,c_2724])).

cnf(c_6779,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6587,c_23,c_25,c_59,c_62,c_3044,c_3078,c_3193,c_4903,c_4904])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2733,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3731,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2733,c_2734])).

cnf(c_6784,plain,
    ( r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6779,c_3731])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_283,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_2257,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_284])).

cnf(c_2719,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2257])).

cnf(c_6956,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6784,c_2719])).

cnf(c_2258,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_284])).

cnf(c_2300,plain,
    ( v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2258])).

cnf(c_7231,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6956,c_23,c_25,c_59,c_62,c_2300,c_3044,c_3078,c_3193,c_4903,c_4904])).

cnf(c_6586,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6572,c_2725])).

cnf(c_6727,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6586,c_23,c_25,c_59,c_62,c_3044,c_3078,c_3193,c_4903,c_4904])).

cnf(c_6732,plain,
    ( r2_hidden(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6727,c_3731])).

cnf(c_6797,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP2_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_6732,c_2719])).

cnf(c_6822,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP2_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6797,c_5131])).

cnf(c_7129,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6822,c_23,c_25,c_59,c_62,c_2300,c_3044,c_3078,c_3193,c_4903,c_4904])).

cnf(c_7234,plain,
    ( sK5 = sK4 ),
    inference(demodulation,[status(thm)],[c_7231,c_7129])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7234,c_5366,c_5122,c_3413,c_3077,c_3043,c_2254,c_2289,c_2283,c_916,c_791,c_666,c_541,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.98/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/0.99  
% 2.98/0.99  ------  iProver source info
% 2.98/0.99  
% 2.98/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.98/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/0.99  git: non_committed_changes: false
% 2.98/0.99  git: last_make_outside_of_git: false
% 2.98/0.99  
% 2.98/0.99  ------ 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options
% 2.98/0.99  
% 2.98/0.99  --out_options                           all
% 2.98/0.99  --tptp_safe_out                         true
% 2.98/0.99  --problem_path                          ""
% 2.98/0.99  --include_path                          ""
% 2.98/0.99  --clausifier                            res/vclausify_rel
% 2.98/0.99  --clausifier_options                    --mode clausify
% 2.98/0.99  --stdin                                 false
% 2.98/0.99  --stats_out                             all
% 2.98/0.99  
% 2.98/0.99  ------ General Options
% 2.98/0.99  
% 2.98/0.99  --fof                                   false
% 2.98/0.99  --time_out_real                         305.
% 2.98/0.99  --time_out_virtual                      -1.
% 2.98/0.99  --symbol_type_check                     false
% 2.98/0.99  --clausify_out                          false
% 2.98/0.99  --sig_cnt_out                           false
% 2.98/0.99  --trig_cnt_out                          false
% 2.98/0.99  --trig_cnt_out_tolerance                1.
% 2.98/0.99  --trig_cnt_out_sk_spl                   false
% 2.98/0.99  --abstr_cl_out                          false
% 2.98/0.99  
% 2.98/0.99  ------ Global Options
% 2.98/0.99  
% 2.98/0.99  --schedule                              default
% 2.98/0.99  --add_important_lit                     false
% 2.98/0.99  --prop_solver_per_cl                    1000
% 2.98/0.99  --min_unsat_core                        false
% 2.98/0.99  --soft_assumptions                      false
% 2.98/0.99  --soft_lemma_size                       3
% 2.98/0.99  --prop_impl_unit_size                   0
% 2.98/0.99  --prop_impl_unit                        []
% 2.98/0.99  --share_sel_clauses                     true
% 2.98/0.99  --reset_solvers                         false
% 2.98/0.99  --bc_imp_inh                            [conj_cone]
% 2.98/0.99  --conj_cone_tolerance                   3.
% 2.98/0.99  --extra_neg_conj                        none
% 2.98/0.99  --large_theory_mode                     true
% 2.98/0.99  --prolific_symb_bound                   200
% 2.98/0.99  --lt_threshold                          2000
% 2.98/0.99  --clause_weak_htbl                      true
% 2.98/0.99  --gc_record_bc_elim                     false
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing Options
% 2.98/0.99  
% 2.98/0.99  --preprocessing_flag                    true
% 2.98/0.99  --time_out_prep_mult                    0.1
% 2.98/0.99  --splitting_mode                        input
% 2.98/0.99  --splitting_grd                         true
% 2.98/0.99  --splitting_cvd                         false
% 2.98/0.99  --splitting_cvd_svl                     false
% 2.98/0.99  --splitting_nvd                         32
% 2.98/0.99  --sub_typing                            true
% 2.98/0.99  --prep_gs_sim                           true
% 2.98/0.99  --prep_unflatten                        true
% 2.98/0.99  --prep_res_sim                          true
% 2.98/0.99  --prep_upred                            true
% 2.98/0.99  --prep_sem_filter                       exhaustive
% 2.98/0.99  --prep_sem_filter_out                   false
% 2.98/0.99  --pred_elim                             true
% 2.98/0.99  --res_sim_input                         true
% 2.98/0.99  --eq_ax_congr_red                       true
% 2.98/0.99  --pure_diseq_elim                       true
% 2.98/0.99  --brand_transform                       false
% 2.98/0.99  --non_eq_to_eq                          false
% 2.98/0.99  --prep_def_merge                        true
% 2.98/0.99  --prep_def_merge_prop_impl              false
% 2.98/0.99  --prep_def_merge_mbd                    true
% 2.98/0.99  --prep_def_merge_tr_red                 false
% 2.98/0.99  --prep_def_merge_tr_cl                  false
% 2.98/0.99  --smt_preprocessing                     true
% 2.98/0.99  --smt_ac_axioms                         fast
% 2.98/0.99  --preprocessed_out                      false
% 2.98/0.99  --preprocessed_stats                    false
% 2.98/0.99  
% 2.98/0.99  ------ Abstraction refinement Options
% 2.98/0.99  
% 2.98/0.99  --abstr_ref                             []
% 2.98/0.99  --abstr_ref_prep                        false
% 2.98/0.99  --abstr_ref_until_sat                   false
% 2.98/0.99  --abstr_ref_sig_restrict                funpre
% 2.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.99  --abstr_ref_under                       []
% 2.98/0.99  
% 2.98/0.99  ------ SAT Options
% 2.98/0.99  
% 2.98/0.99  --sat_mode                              false
% 2.98/0.99  --sat_fm_restart_options                ""
% 2.98/0.99  --sat_gr_def                            false
% 2.98/0.99  --sat_epr_types                         true
% 2.98/0.99  --sat_non_cyclic_types                  false
% 2.98/0.99  --sat_finite_models                     false
% 2.98/0.99  --sat_fm_lemmas                         false
% 2.98/0.99  --sat_fm_prep                           false
% 2.98/0.99  --sat_fm_uc_incr                        true
% 2.98/0.99  --sat_out_model                         small
% 2.98/0.99  --sat_out_clauses                       false
% 2.98/0.99  
% 2.98/0.99  ------ QBF Options
% 2.98/0.99  
% 2.98/0.99  --qbf_mode                              false
% 2.98/0.99  --qbf_elim_univ                         false
% 2.98/0.99  --qbf_dom_inst                          none
% 2.98/0.99  --qbf_dom_pre_inst                      false
% 2.98/0.99  --qbf_sk_in                             false
% 2.98/0.99  --qbf_pred_elim                         true
% 2.98/0.99  --qbf_split                             512
% 2.98/0.99  
% 2.98/0.99  ------ BMC1 Options
% 2.98/0.99  
% 2.98/0.99  --bmc1_incremental                      false
% 2.98/0.99  --bmc1_axioms                           reachable_all
% 2.98/0.99  --bmc1_min_bound                        0
% 2.98/0.99  --bmc1_max_bound                        -1
% 2.98/0.99  --bmc1_max_bound_default                -1
% 2.98/0.99  --bmc1_symbol_reachability              true
% 2.98/0.99  --bmc1_property_lemmas                  false
% 2.98/0.99  --bmc1_k_induction                      false
% 2.98/0.99  --bmc1_non_equiv_states                 false
% 2.98/0.99  --bmc1_deadlock                         false
% 2.98/0.99  --bmc1_ucm                              false
% 2.98/0.99  --bmc1_add_unsat_core                   none
% 2.98/0.99  --bmc1_unsat_core_children              false
% 2.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.99  --bmc1_out_stat                         full
% 2.98/0.99  --bmc1_ground_init                      false
% 2.98/0.99  --bmc1_pre_inst_next_state              false
% 2.98/0.99  --bmc1_pre_inst_state                   false
% 2.98/0.99  --bmc1_pre_inst_reach_state             false
% 2.98/0.99  --bmc1_out_unsat_core                   false
% 2.98/0.99  --bmc1_aig_witness_out                  false
% 2.98/0.99  --bmc1_verbose                          false
% 2.98/0.99  --bmc1_dump_clauses_tptp                false
% 2.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.99  --bmc1_dump_file                        -
% 2.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.99  --bmc1_ucm_extend_mode                  1
% 2.98/0.99  --bmc1_ucm_init_mode                    2
% 2.98/0.99  --bmc1_ucm_cone_mode                    none
% 2.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.99  --bmc1_ucm_relax_model                  4
% 2.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.99  --bmc1_ucm_layered_model                none
% 2.98/0.99  --bmc1_ucm_max_lemma_size               10
% 2.98/0.99  
% 2.98/0.99  ------ AIG Options
% 2.98/0.99  
% 2.98/0.99  --aig_mode                              false
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation Options
% 2.98/0.99  
% 2.98/0.99  --instantiation_flag                    true
% 2.98/0.99  --inst_sos_flag                         false
% 2.98/0.99  --inst_sos_phase                        true
% 2.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel_side                     num_symb
% 2.98/0.99  --inst_solver_per_active                1400
% 2.98/0.99  --inst_solver_calls_frac                1.
% 2.98/0.99  --inst_passive_queue_type               priority_queues
% 2.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.99  --inst_passive_queues_freq              [25;2]
% 2.98/0.99  --inst_dismatching                      true
% 2.98/0.99  --inst_eager_unprocessed_to_passive     true
% 2.98/0.99  --inst_prop_sim_given                   true
% 2.98/0.99  --inst_prop_sim_new                     false
% 2.98/0.99  --inst_subs_new                         false
% 2.98/0.99  --inst_eq_res_simp                      false
% 2.98/0.99  --inst_subs_given                       false
% 2.98/0.99  --inst_orphan_elimination               true
% 2.98/0.99  --inst_learning_loop_flag               true
% 2.98/0.99  --inst_learning_start                   3000
% 2.98/0.99  --inst_learning_factor                  2
% 2.98/0.99  --inst_start_prop_sim_after_learn       3
% 2.98/0.99  --inst_sel_renew                        solver
% 2.98/0.99  --inst_lit_activity_flag                true
% 2.98/0.99  --inst_restr_to_given                   false
% 2.98/0.99  --inst_activity_threshold               500
% 2.98/0.99  --inst_out_proof                        true
% 2.98/0.99  
% 2.98/0.99  ------ Resolution Options
% 2.98/0.99  
% 2.98/0.99  --resolution_flag                       true
% 2.98/0.99  --res_lit_sel                           adaptive
% 2.98/0.99  --res_lit_sel_side                      none
% 2.98/0.99  --res_ordering                          kbo
% 2.98/0.99  --res_to_prop_solver                    active
% 2.98/0.99  --res_prop_simpl_new                    false
% 2.98/0.99  --res_prop_simpl_given                  true
% 2.98/0.99  --res_passive_queue_type                priority_queues
% 2.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.99  --res_passive_queues_freq               [15;5]
% 2.98/0.99  --res_forward_subs                      full
% 2.98/0.99  --res_backward_subs                     full
% 2.98/0.99  --res_forward_subs_resolution           true
% 2.98/0.99  --res_backward_subs_resolution          true
% 2.98/0.99  --res_orphan_elimination                true
% 2.98/0.99  --res_time_limit                        2.
% 2.98/0.99  --res_out_proof                         true
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Options
% 2.98/0.99  
% 2.98/0.99  --superposition_flag                    true
% 2.98/0.99  --sup_passive_queue_type                priority_queues
% 2.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.99  --demod_completeness_check              fast
% 2.98/0.99  --demod_use_ground                      true
% 2.98/0.99  --sup_to_prop_solver                    passive
% 2.98/0.99  --sup_prop_simpl_new                    true
% 2.98/0.99  --sup_prop_simpl_given                  true
% 2.98/0.99  --sup_fun_splitting                     false
% 2.98/0.99  --sup_smt_interval                      50000
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Simplification Setup
% 2.98/0.99  
% 2.98/0.99  --sup_indices_passive                   []
% 2.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_full_bw                           [BwDemod]
% 2.98/0.99  --sup_immed_triv                        [TrivRules]
% 2.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_immed_bw_main                     []
% 2.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  
% 2.98/0.99  ------ Combination Options
% 2.98/0.99  
% 2.98/0.99  --comb_res_mult                         3
% 2.98/0.99  --comb_sup_mult                         2
% 2.98/0.99  --comb_inst_mult                        10
% 2.98/0.99  
% 2.98/0.99  ------ Debug Options
% 2.98/0.99  
% 2.98/0.99  --dbg_backtrace                         false
% 2.98/0.99  --dbg_dump_prop_clauses                 false
% 2.98/0.99  --dbg_dump_prop_clauses_file            -
% 2.98/0.99  --dbg_out_stat                          false
% 2.98/0.99  ------ Parsing...
% 2.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/0.99  ------ Proving...
% 2.98/0.99  ------ Problem Properties 
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  clauses                                 25
% 2.98/0.99  conjectures                             6
% 2.98/0.99  EPR                                     7
% 2.98/0.99  Horn                                    20
% 2.98/0.99  unary                                   3
% 2.98/0.99  binary                                  6
% 2.98/0.99  lits                                    67
% 2.98/0.99  lits eq                                 13
% 2.98/0.99  fd_pure                                 0
% 2.98/0.99  fd_pseudo                               0
% 2.98/0.99  fd_cond                                 0
% 2.98/0.99  fd_pseudo_cond                          2
% 2.98/0.99  AC symbols                              0
% 2.98/0.99  
% 2.98/0.99  ------ Schedule dynamic 5 is on 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  ------ 
% 2.98/0.99  Current options:
% 2.98/0.99  ------ 
% 2.98/0.99  
% 2.98/0.99  ------ Input Options
% 2.98/0.99  
% 2.98/0.99  --out_options                           all
% 2.98/0.99  --tptp_safe_out                         true
% 2.98/0.99  --problem_path                          ""
% 2.98/0.99  --include_path                          ""
% 2.98/0.99  --clausifier                            res/vclausify_rel
% 2.98/0.99  --clausifier_options                    --mode clausify
% 2.98/0.99  --stdin                                 false
% 2.98/0.99  --stats_out                             all
% 2.98/0.99  
% 2.98/0.99  ------ General Options
% 2.98/0.99  
% 2.98/0.99  --fof                                   false
% 2.98/0.99  --time_out_real                         305.
% 2.98/0.99  --time_out_virtual                      -1.
% 2.98/0.99  --symbol_type_check                     false
% 2.98/0.99  --clausify_out                          false
% 2.98/0.99  --sig_cnt_out                           false
% 2.98/0.99  --trig_cnt_out                          false
% 2.98/0.99  --trig_cnt_out_tolerance                1.
% 2.98/0.99  --trig_cnt_out_sk_spl                   false
% 2.98/0.99  --abstr_cl_out                          false
% 2.98/0.99  
% 2.98/0.99  ------ Global Options
% 2.98/0.99  
% 2.98/0.99  --schedule                              default
% 2.98/0.99  --add_important_lit                     false
% 2.98/0.99  --prop_solver_per_cl                    1000
% 2.98/0.99  --min_unsat_core                        false
% 2.98/0.99  --soft_assumptions                      false
% 2.98/0.99  --soft_lemma_size                       3
% 2.98/0.99  --prop_impl_unit_size                   0
% 2.98/0.99  --prop_impl_unit                        []
% 2.98/0.99  --share_sel_clauses                     true
% 2.98/0.99  --reset_solvers                         false
% 2.98/0.99  --bc_imp_inh                            [conj_cone]
% 2.98/0.99  --conj_cone_tolerance                   3.
% 2.98/0.99  --extra_neg_conj                        none
% 2.98/0.99  --large_theory_mode                     true
% 2.98/0.99  --prolific_symb_bound                   200
% 2.98/0.99  --lt_threshold                          2000
% 2.98/0.99  --clause_weak_htbl                      true
% 2.98/0.99  --gc_record_bc_elim                     false
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing Options
% 2.98/0.99  
% 2.98/0.99  --preprocessing_flag                    true
% 2.98/0.99  --time_out_prep_mult                    0.1
% 2.98/0.99  --splitting_mode                        input
% 2.98/0.99  --splitting_grd                         true
% 2.98/0.99  --splitting_cvd                         false
% 2.98/0.99  --splitting_cvd_svl                     false
% 2.98/0.99  --splitting_nvd                         32
% 2.98/0.99  --sub_typing                            true
% 2.98/0.99  --prep_gs_sim                           true
% 2.98/0.99  --prep_unflatten                        true
% 2.98/0.99  --prep_res_sim                          true
% 2.98/0.99  --prep_upred                            true
% 2.98/0.99  --prep_sem_filter                       exhaustive
% 2.98/0.99  --prep_sem_filter_out                   false
% 2.98/0.99  --pred_elim                             true
% 2.98/0.99  --res_sim_input                         true
% 2.98/0.99  --eq_ax_congr_red                       true
% 2.98/0.99  --pure_diseq_elim                       true
% 2.98/0.99  --brand_transform                       false
% 2.98/0.99  --non_eq_to_eq                          false
% 2.98/0.99  --prep_def_merge                        true
% 2.98/0.99  --prep_def_merge_prop_impl              false
% 2.98/0.99  --prep_def_merge_mbd                    true
% 2.98/0.99  --prep_def_merge_tr_red                 false
% 2.98/0.99  --prep_def_merge_tr_cl                  false
% 2.98/0.99  --smt_preprocessing                     true
% 2.98/0.99  --smt_ac_axioms                         fast
% 2.98/0.99  --preprocessed_out                      false
% 2.98/0.99  --preprocessed_stats                    false
% 2.98/0.99  
% 2.98/0.99  ------ Abstraction refinement Options
% 2.98/0.99  
% 2.98/0.99  --abstr_ref                             []
% 2.98/0.99  --abstr_ref_prep                        false
% 2.98/0.99  --abstr_ref_until_sat                   false
% 2.98/0.99  --abstr_ref_sig_restrict                funpre
% 2.98/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.99  --abstr_ref_under                       []
% 2.98/0.99  
% 2.98/0.99  ------ SAT Options
% 2.98/0.99  
% 2.98/0.99  --sat_mode                              false
% 2.98/0.99  --sat_fm_restart_options                ""
% 2.98/0.99  --sat_gr_def                            false
% 2.98/0.99  --sat_epr_types                         true
% 2.98/0.99  --sat_non_cyclic_types                  false
% 2.98/0.99  --sat_finite_models                     false
% 2.98/0.99  --sat_fm_lemmas                         false
% 2.98/0.99  --sat_fm_prep                           false
% 2.98/0.99  --sat_fm_uc_incr                        true
% 2.98/0.99  --sat_out_model                         small
% 2.98/0.99  --sat_out_clauses                       false
% 2.98/0.99  
% 2.98/0.99  ------ QBF Options
% 2.98/0.99  
% 2.98/0.99  --qbf_mode                              false
% 2.98/0.99  --qbf_elim_univ                         false
% 2.98/0.99  --qbf_dom_inst                          none
% 2.98/0.99  --qbf_dom_pre_inst                      false
% 2.98/0.99  --qbf_sk_in                             false
% 2.98/0.99  --qbf_pred_elim                         true
% 2.98/0.99  --qbf_split                             512
% 2.98/0.99  
% 2.98/0.99  ------ BMC1 Options
% 2.98/0.99  
% 2.98/0.99  --bmc1_incremental                      false
% 2.98/0.99  --bmc1_axioms                           reachable_all
% 2.98/0.99  --bmc1_min_bound                        0
% 2.98/0.99  --bmc1_max_bound                        -1
% 2.98/0.99  --bmc1_max_bound_default                -1
% 2.98/0.99  --bmc1_symbol_reachability              true
% 2.98/0.99  --bmc1_property_lemmas                  false
% 2.98/0.99  --bmc1_k_induction                      false
% 2.98/0.99  --bmc1_non_equiv_states                 false
% 2.98/0.99  --bmc1_deadlock                         false
% 2.98/0.99  --bmc1_ucm                              false
% 2.98/0.99  --bmc1_add_unsat_core                   none
% 2.98/0.99  --bmc1_unsat_core_children              false
% 2.98/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.99  --bmc1_out_stat                         full
% 2.98/0.99  --bmc1_ground_init                      false
% 2.98/0.99  --bmc1_pre_inst_next_state              false
% 2.98/0.99  --bmc1_pre_inst_state                   false
% 2.98/0.99  --bmc1_pre_inst_reach_state             false
% 2.98/0.99  --bmc1_out_unsat_core                   false
% 2.98/0.99  --bmc1_aig_witness_out                  false
% 2.98/0.99  --bmc1_verbose                          false
% 2.98/0.99  --bmc1_dump_clauses_tptp                false
% 2.98/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.99  --bmc1_dump_file                        -
% 2.98/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.99  --bmc1_ucm_extend_mode                  1
% 2.98/0.99  --bmc1_ucm_init_mode                    2
% 2.98/0.99  --bmc1_ucm_cone_mode                    none
% 2.98/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.99  --bmc1_ucm_relax_model                  4
% 2.98/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.99  --bmc1_ucm_layered_model                none
% 2.98/0.99  --bmc1_ucm_max_lemma_size               10
% 2.98/0.99  
% 2.98/0.99  ------ AIG Options
% 2.98/0.99  
% 2.98/0.99  --aig_mode                              false
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation Options
% 2.98/0.99  
% 2.98/0.99  --instantiation_flag                    true
% 2.98/0.99  --inst_sos_flag                         false
% 2.98/0.99  --inst_sos_phase                        true
% 2.98/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.99  --inst_lit_sel_side                     none
% 2.98/0.99  --inst_solver_per_active                1400
% 2.98/0.99  --inst_solver_calls_frac                1.
% 2.98/0.99  --inst_passive_queue_type               priority_queues
% 2.98/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.99  --inst_passive_queues_freq              [25;2]
% 2.98/0.99  --inst_dismatching                      true
% 2.98/0.99  --inst_eager_unprocessed_to_passive     true
% 2.98/0.99  --inst_prop_sim_given                   true
% 2.98/0.99  --inst_prop_sim_new                     false
% 2.98/0.99  --inst_subs_new                         false
% 2.98/0.99  --inst_eq_res_simp                      false
% 2.98/0.99  --inst_subs_given                       false
% 2.98/0.99  --inst_orphan_elimination               true
% 2.98/0.99  --inst_learning_loop_flag               true
% 2.98/0.99  --inst_learning_start                   3000
% 2.98/0.99  --inst_learning_factor                  2
% 2.98/0.99  --inst_start_prop_sim_after_learn       3
% 2.98/0.99  --inst_sel_renew                        solver
% 2.98/0.99  --inst_lit_activity_flag                true
% 2.98/0.99  --inst_restr_to_given                   false
% 2.98/0.99  --inst_activity_threshold               500
% 2.98/0.99  --inst_out_proof                        true
% 2.98/0.99  
% 2.98/0.99  ------ Resolution Options
% 2.98/0.99  
% 2.98/0.99  --resolution_flag                       false
% 2.98/0.99  --res_lit_sel                           adaptive
% 2.98/0.99  --res_lit_sel_side                      none
% 2.98/0.99  --res_ordering                          kbo
% 2.98/0.99  --res_to_prop_solver                    active
% 2.98/0.99  --res_prop_simpl_new                    false
% 2.98/0.99  --res_prop_simpl_given                  true
% 2.98/0.99  --res_passive_queue_type                priority_queues
% 2.98/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.99  --res_passive_queues_freq               [15;5]
% 2.98/0.99  --res_forward_subs                      full
% 2.98/0.99  --res_backward_subs                     full
% 2.98/0.99  --res_forward_subs_resolution           true
% 2.98/0.99  --res_backward_subs_resolution          true
% 2.98/0.99  --res_orphan_elimination                true
% 2.98/0.99  --res_time_limit                        2.
% 2.98/0.99  --res_out_proof                         true
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Options
% 2.98/0.99  
% 2.98/0.99  --superposition_flag                    true
% 2.98/0.99  --sup_passive_queue_type                priority_queues
% 2.98/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.99  --demod_completeness_check              fast
% 2.98/0.99  --demod_use_ground                      true
% 2.98/0.99  --sup_to_prop_solver                    passive
% 2.98/0.99  --sup_prop_simpl_new                    true
% 2.98/0.99  --sup_prop_simpl_given                  true
% 2.98/0.99  --sup_fun_splitting                     false
% 2.98/0.99  --sup_smt_interval                      50000
% 2.98/0.99  
% 2.98/0.99  ------ Superposition Simplification Setup
% 2.98/0.99  
% 2.98/0.99  --sup_indices_passive                   []
% 2.98/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_full_bw                           [BwDemod]
% 2.98/0.99  --sup_immed_triv                        [TrivRules]
% 2.98/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_immed_bw_main                     []
% 2.98/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.99  
% 2.98/0.99  ------ Combination Options
% 2.98/0.99  
% 2.98/0.99  --comb_res_mult                         3
% 2.98/0.99  --comb_sup_mult                         2
% 2.98/0.99  --comb_inst_mult                        10
% 2.98/0.99  
% 2.98/0.99  ------ Debug Options
% 2.98/0.99  
% 2.98/0.99  --dbg_backtrace                         false
% 2.98/0.99  --dbg_dump_prop_clauses                 false
% 2.98/0.99  --dbg_dump_prop_clauses_file            -
% 2.98/0.99  --dbg_out_stat                          false
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  ------ Proving...
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  % SZS status Theorem for theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  fof(f6,axiom,(
% 2.98/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f17,plain,(
% 2.98/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f6])).
% 2.98/0.99  
% 2.98/0.99  fof(f18,plain,(
% 2.98/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.98/0.99    inference(flattening,[],[f17])).
% 2.98/0.99  
% 2.98/0.99  fof(f27,plain,(
% 2.98/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.98/0.99    inference(nnf_transformation,[],[f18])).
% 2.98/0.99  
% 2.98/0.99  fof(f28,plain,(
% 2.98/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.98/0.99    inference(rectify,[],[f27])).
% 2.98/0.99  
% 2.98/0.99  fof(f29,plain,(
% 2.98/0.99    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f30,plain,(
% 2.98/0.99    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 2.98/0.99  
% 2.98/0.99  fof(f45,plain,(
% 2.98/0.99    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f30])).
% 2.98/0.99  
% 2.98/0.99  fof(f11,conjecture,(
% 2.98/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f12,negated_conjecture,(
% 2.98/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 2.98/0.99    inference(negated_conjecture,[],[f11])).
% 2.98/0.99  
% 2.98/0.99  fof(f25,plain,(
% 2.98/0.99    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.98/0.99    inference(ennf_transformation,[],[f12])).
% 2.98/0.99  
% 2.98/0.99  fof(f26,plain,(
% 2.98/0.99    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.98/0.99    inference(flattening,[],[f25])).
% 2.98/0.99  
% 2.98/0.99  fof(f31,plain,(
% 2.98/0.99    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.98/0.99    inference(nnf_transformation,[],[f26])).
% 2.98/0.99  
% 2.98/0.99  fof(f32,plain,(
% 2.98/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.98/0.99    inference(flattening,[],[f31])).
% 2.98/0.99  
% 2.98/0.99  fof(f33,plain,(
% 2.98/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.98/0.99    inference(rectify,[],[f32])).
% 2.98/0.99  
% 2.98/0.99  fof(f35,plain,(
% 2.98/0.99    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f34,plain,(
% 2.98/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 2.98/0.99    introduced(choice_axiom,[])).
% 2.98/0.99  
% 2.98/0.99  fof(f36,plain,(
% 2.98/0.99    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 2.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f35,f34])).
% 2.98/0.99  
% 2.98/0.99  fof(f52,plain,(
% 2.98/0.99    v1_funct_1(sK3)),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f54,plain,(
% 2.98/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f4,axiom,(
% 2.98/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f16,plain,(
% 2.98/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.98/0.99    inference(ennf_transformation,[],[f4])).
% 2.98/0.99  
% 2.98/0.99  fof(f40,plain,(
% 2.98/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f16])).
% 2.98/0.99  
% 2.98/0.99  fof(f5,axiom,(
% 2.98/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f41,plain,(
% 2.98/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f5])).
% 2.98/0.99  
% 2.98/0.99  fof(f10,axiom,(
% 2.98/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f23,plain,(
% 2.98/0.99    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.98/0.99    inference(ennf_transformation,[],[f10])).
% 2.98/0.99  
% 2.98/0.99  fof(f24,plain,(
% 2.98/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.98/0.99    inference(flattening,[],[f23])).
% 2.98/0.99  
% 2.98/0.99  fof(f51,plain,(
% 2.98/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f24])).
% 2.98/0.99  
% 2.98/0.99  fof(f53,plain,(
% 2.98/0.99    v1_funct_2(sK3,sK2,sK2)),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f56,plain,(
% 2.98/0.99    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f46,plain,(
% 2.98/0.99    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f30])).
% 2.98/0.99  
% 2.98/0.99  fof(f59,plain,(
% 2.98/0.99    sK4 != sK5 | ~v2_funct_1(sK3)),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f44,plain,(
% 2.98/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f30])).
% 2.98/0.99  
% 2.98/0.99  fof(f43,plain,(
% 2.98/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f30])).
% 2.98/0.99  
% 2.98/0.99  fof(f42,plain,(
% 2.98/0.99    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f30])).
% 2.98/0.99  
% 2.98/0.99  fof(f9,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f22,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.99    inference(ennf_transformation,[],[f9])).
% 2.98/0.99  
% 2.98/0.99  fof(f50,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f22])).
% 2.98/0.99  
% 2.98/0.99  fof(f8,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f21,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.98/0.99    inference(ennf_transformation,[],[f8])).
% 2.98/0.99  
% 2.98/0.99  fof(f49,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f21])).
% 2.98/0.99  
% 2.98/0.99  fof(f3,axiom,(
% 2.98/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f14,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.98/0.99    inference(ennf_transformation,[],[f3])).
% 2.98/0.99  
% 2.98/0.99  fof(f15,plain,(
% 2.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.98/0.99    inference(flattening,[],[f14])).
% 2.98/0.99  
% 2.98/0.99  fof(f39,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f15])).
% 2.98/0.99  
% 2.98/0.99  fof(f55,plain,(
% 2.98/0.99    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f1,axiom,(
% 2.98/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f13,plain,(
% 2.98/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.98/0.99    inference(ennf_transformation,[],[f1])).
% 2.98/0.99  
% 2.98/0.99  fof(f37,plain,(
% 2.98/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f13])).
% 2.98/0.99  
% 2.98/0.99  fof(f57,plain,(
% 2.98/0.99    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f58,plain,(
% 2.98/0.99    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 2.98/0.99    inference(cnf_transformation,[],[f36])).
% 2.98/0.99  
% 2.98/0.99  fof(f2,axiom,(
% 2.98/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f38,plain,(
% 2.98/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.98/0.99    inference(cnf_transformation,[],[f2])).
% 2.98/0.99  
% 2.98/0.99  fof(f7,axiom,(
% 2.98/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 2.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/0.99  
% 2.98/0.99  fof(f19,plain,(
% 2.98/0.99    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.98/0.99    inference(ennf_transformation,[],[f7])).
% 2.98/0.99  
% 2.98/0.99  fof(f20,plain,(
% 2.98/0.99    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.98/0.99    inference(flattening,[],[f19])).
% 2.98/0.99  
% 2.98/0.99  fof(f47,plain,(
% 2.98/0.99    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.98/0.99    inference(cnf_transformation,[],[f20])).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6,plain,
% 2.98/0.99      ( ~ v1_funct_1(X0)
% 2.98/0.99      | v2_funct_1(X0)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_22,negated_conjecture,
% 2.98/0.99      ( v1_funct_1(sK3) ),
% 2.98/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_369,plain,
% 2.98/0.99      ( v2_funct_1(X0)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
% 2.98/0.99      | sK3 != X0 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_370,plain,
% 2.98/0.99      ( v2_funct_1(sK3)
% 2.98/0.99      | ~ v1_relat_1(sK3)
% 2.98/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_369]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2711,plain,
% 2.98/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_20,negated_conjecture,
% 2.98/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 2.98/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_25,plain,
% 2.98/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_371,plain,
% 2.98/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.98/0.99      | ~ v1_relat_1(X1)
% 2.98/0.99      | v1_relat_1(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2934,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | v1_relat_1(X0)
% 2.98/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3043,plain,
% 2.98/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.98/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
% 2.98/0.99      | v1_relat_1(sK3) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_2934]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3044,plain,
% 2.98/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 2.98/0.99      | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 2.98/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_3043]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4,plain,
% 2.98/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3077,plain,
% 2.98/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3078,plain,
% 2.98/0.99      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_3077]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3473,plain,
% 2.98/0.99      ( v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3)) ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_2711,c_25,c_371,c_3044,c_3078]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3474,plain,
% 2.98/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_3473]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_14,plain,
% 2.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ r2_hidden(X3,X1)
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | ~ v2_funct_1(X0)
% 2.98/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.98/0.99      | k1_xboole_0 = X2 ),
% 2.98/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_21,negated_conjecture,
% 2.98/0.99      ( v1_funct_2(sK3,sK2,sK2) ),
% 2.98/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_254,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | ~ r2_hidden(X3,X1)
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | ~ v2_funct_1(X0)
% 2.98/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 2.98/0.99      | sK2 != X2
% 2.98/0.99      | sK2 != X1
% 2.98/0.99      | sK3 != X0
% 2.98/0.99      | k1_xboole_0 = X2 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_255,plain,
% 2.98/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 2.98/0.99      | ~ r2_hidden(X0,sK2)
% 2.98/0.99      | ~ v1_funct_1(sK3)
% 2.98/0.99      | ~ v2_funct_1(sK3)
% 2.98/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.98/0.99      | k1_xboole_0 = sK2 ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_254]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_259,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,sK2)
% 2.98/0.99      | ~ v2_funct_1(sK3)
% 2.98/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.98/0.99      | k1_xboole_0 = sK2 ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_255,c_22,c_20]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2260,plain,
% 2.98/0.99      ( ~ v2_funct_1(sK3) | sP3_iProver_split | k1_xboole_0 = sK2 ),
% 2.98/0.99      inference(splitting,
% 2.98/0.99                [splitting(split),new_symbols(definition,[])],
% 2.98/0.99                [c_259]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2720,plain,
% 2.98/0.99      ( k1_xboole_0 = sK2
% 2.98/0.99      | v2_funct_1(sK3) != iProver_top
% 2.98/0.99      | sP3_iProver_split = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2260]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3899,plain,
% 2.98/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.98/0.99      | sK2 = k1_xboole_0
% 2.98/0.99      | sP3_iProver_split = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_3474,c_2720]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_18,negated_conjecture,
% 2.98/0.99      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 2.98/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2724,plain,
% 2.98/0.99      ( r2_hidden(sK4,sK2) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2259,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,sK2)
% 2.98/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.98/0.99      | ~ sP3_iProver_split ),
% 2.98/0.99      inference(splitting,
% 2.98/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.98/0.99                [c_259]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2721,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.98/0.99      | r2_hidden(X0,sK2) != iProver_top
% 2.98/0.99      | sP3_iProver_split != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2259]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3355,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.98/0.99      | v2_funct_1(sK3) != iProver_top
% 2.98/0.99      | sP3_iProver_split != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2724,c_2721]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3479,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.98/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.98/0.99      | sP3_iProver_split != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_3474,c_3355]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4458,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.98/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.98/0.99      | sK2 = k1_xboole_0 ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_3899,c_3479]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5,plain,
% 2.98/0.99      ( ~ v1_funct_1(X0)
% 2.98/0.99      | v2_funct_1(X0)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | sK1(X0) != sK0(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_382,plain,
% 2.98/0.99      ( v2_funct_1(X0)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | sK1(X0) != sK0(X0)
% 2.98/0.99      | sK3 != X0 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_383,plain,
% 2.98/0.99      ( v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_382]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_15,negated_conjecture,
% 2.98/0.99      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 2.98/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_541,plain,
% 2.98/0.99      ( ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) | sK5 != sK4 ),
% 2.98/0.99      inference(resolution,[status(thm)],[c_383,c_15]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_666,plain,
% 2.98/0.99      ( ~ v1_relat_1(sK3)
% 2.98/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 2.98/0.99      | sK5 != sK4 ),
% 2.98/0.99      inference(resolution,[status(thm)],[c_370,c_15]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7,plain,
% 2.98/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | v2_funct_1(X0)
% 2.98/0.99      | ~ v1_relat_1(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_356,plain,
% 2.98/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 2.98/0.99      | v2_funct_1(X0)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | sK3 != X0 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_357,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.98/0.99      | v2_funct_1(sK3)
% 2.98/0.99      | ~ v1_relat_1(sK3) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_356]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_791,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.98/0.99      | ~ v1_relat_1(sK3)
% 2.98/0.99      | sK5 != sK4 ),
% 2.98/0.99      inference(resolution,[status(thm)],[c_357,c_15]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_8,plain,
% 2.98/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.98/0.99      | ~ v1_funct_1(X0)
% 2.98/0.99      | v2_funct_1(X0)
% 2.98/0.99      | ~ v1_relat_1(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_343,plain,
% 2.98/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 2.98/0.99      | v2_funct_1(X0)
% 2.98/0.99      | ~ v1_relat_1(X0)
% 2.98/0.99      | sK3 != X0 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_344,plain,
% 2.98/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.98/0.99      | v2_funct_1(sK3)
% 2.98/0.99      | ~ v1_relat_1(sK3) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_343]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_916,plain,
% 2.98/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.98/0.99      | ~ v1_relat_1(sK3)
% 2.98/0.99      | sK5 != sK4 ),
% 2.98/0.99      inference(resolution,[status(thm)],[c_344,c_15]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2271,plain,( X0 != X1 | sK1(X0) = sK1(X1) ),theory(equality) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2283,plain,
% 2.98/0.99      ( sK1(sK3) = sK1(sK3) | sK3 != sK3 ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_2271]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2262,plain,( X0 = X0 ),theory(equality) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2289,plain,
% 2.98/0.99      ( sK3 = sK3 ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_2262]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_9,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.98/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.98/0.99      | ~ v1_funct_1(X1)
% 2.98/0.99      | ~ v2_funct_1(X1)
% 2.98/0.99      | ~ v1_relat_1(X1)
% 2.98/0.99      | X0 = X2
% 2.98/0.99      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 2.98/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_319,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.98/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.98/0.99      | ~ v2_funct_1(X1)
% 2.98/0.99      | ~ v1_relat_1(X1)
% 2.98/0.99      | X2 = X0
% 2.98/0.99      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 2.98/0.99      | sK3 != X1 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_320,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.98/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.98/0.99      | ~ v2_funct_1(sK3)
% 2.98/0.99      | ~ v1_relat_1(sK3)
% 2.98/0.99      | X1 = X0
% 2.98/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_319]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2254,plain,
% 2.98/0.99      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sP0_iProver_split ),
% 2.98/0.99      inference(splitting,
% 2.98/0.99                [splitting(split),new_symbols(definition,[])],
% 2.98/0.99                [c_320]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2263,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3195,plain,
% 2.98/0.99      ( sK1(sK3) != X0 | sK1(sK3) = sK0(sK3) | sK0(sK3) != X0 ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_2263]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3413,plain,
% 2.98/0.99      ( sK1(sK3) != sK1(sK3)
% 2.98/0.99      | sK1(sK3) = sK0(sK3)
% 2.98/0.99      | sK0(sK3) != sK1(sK3) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_3195]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2713,plain,
% 2.98/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_23,plain,
% 2.98/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_51,plain,
% 2.98/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0)) = iProver_top
% 2.98/0.99      | v1_funct_1(X0) != iProver_top
% 2.98/0.99      | v2_funct_1(X0) = iProver_top
% 2.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_53,plain,
% 2.98/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.98/0.99      | v1_funct_1(sK3) != iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_51]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4087,plain,
% 2.98/0.99      ( v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_2713,c_23,c_25,c_53,c_3044,c_3078]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4088,plain,
% 2.98/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_4087]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2722,plain,
% 2.98/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_13,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2728,plain,
% 2.98/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3156,plain,
% 2.98/0.99      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2722,c_2728]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_12,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.98/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2729,plain,
% 2.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.98/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3597,plain,
% 2.98/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.98/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_3156,c_2729]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4239,plain,
% 2.98/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_3597,c_25]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2,plain,
% 2.98/0.99      ( m1_subset_1(X0,X1)
% 2.98/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.98/0.99      | ~ r2_hidden(X0,X2) ),
% 2.98/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2732,plain,
% 2.98/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.98/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4244,plain,
% 2.98/0.99      ( m1_subset_1(X0,sK2) = iProver_top
% 2.98/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_4239,c_2732]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4824,plain,
% 2.98/0.99      ( m1_subset_1(sK0(sK3),sK2) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_4088,c_4244]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_57,plain,
% 2.98/0.99      ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 2.98/0.99      | v1_funct_1(X0) != iProver_top
% 2.98/0.99      | v2_funct_1(X0) = iProver_top
% 2.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_59,plain,
% 2.98/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 2.98/0.99      | v1_funct_1(sK3) != iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_57]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_60,plain,
% 2.98/0.99      ( sK1(X0) != sK0(X0)
% 2.98/0.99      | v1_funct_1(X0) != iProver_top
% 2.98/0.99      | v2_funct_1(X0) = iProver_top
% 2.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_62,plain,
% 2.98/0.99      ( sK1(sK3) != sK0(sK3)
% 2.98/0.99      | v1_funct_1(sK3) != iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_60]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_19,negated_conjecture,
% 2.98/0.99      ( ~ r2_hidden(X0,sK2)
% 2.98/0.99      | ~ r2_hidden(X1,sK2)
% 2.98/0.99      | v2_funct_1(sK3)
% 2.98/0.99      | X1 = X0
% 2.98/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 2.98/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3192,plain,
% 2.98/0.99      ( ~ r2_hidden(sK1(sK3),sK2)
% 2.98/0.99      | ~ r2_hidden(sK0(sK3),sK2)
% 2.98/0.99      | v2_funct_1(sK3)
% 2.98/0.99      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.98/0.99      | sK1(sK3) = sK0(sK3) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3193,plain,
% 2.98/0.99      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 2.98/0.99      | sK1(sK3) = sK0(sK3)
% 2.98/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 2.98/0.99      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_3192]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_0,plain,
% 2.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.98/0.99      | ~ r2_hidden(X2,X0)
% 2.98/0.99      | r2_hidden(X2,X1) ),
% 2.98/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2734,plain,
% 2.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.98/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.98/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4245,plain,
% 2.98/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.98/0.99      | r2_hidden(X0,sK2) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_4239,c_2734]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4903,plain,
% 2.98/0.99      ( r2_hidden(sK0(sK3),sK2) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_4088,c_4245]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2712,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_54,plain,
% 2.98/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0)) = iProver_top
% 2.98/0.99      | v1_funct_1(X0) != iProver_top
% 2.98/0.99      | v2_funct_1(X0) = iProver_top
% 2.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_56,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.98/0.99      | v1_funct_1(sK3) != iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_54]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3995,plain,
% 2.98/0.99      ( v2_funct_1(sK3) = iProver_top
% 2.98/0.99      | r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_2712,c_23,c_25,c_56,c_3044,c_3078]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3996,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(renaming,[status(thm)],[c_3995]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_4904,plain,
% 2.98/0.99      ( r2_hidden(sK1(sK3),sK2) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_3996,c_4245]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5120,plain,
% 2.98/0.99      ( v2_funct_1(sK3) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_4824,c_23,c_25,c_59,c_62,c_3044,c_3078,c_3193,c_4903,
% 2.98/0.99                 c_4904]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5122,plain,
% 2.98/0.99      ( v2_funct_1(sK3) ),
% 2.98/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5120]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2253,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.98/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 2.98/0.99      | X1 = X0
% 2.98/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
% 2.98/0.99      | ~ sP0_iProver_split ),
% 2.98/0.99      inference(splitting,
% 2.98/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.98/0.99                [c_320]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5364,plain,
% 2.98/0.99      ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
% 2.98/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.98/0.99      | ~ sP0_iProver_split
% 2.98/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
% 2.98/0.99      | sK0(sK3) = sK1(X0) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_2253]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5366,plain,
% 2.98/0.99      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 2.98/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 2.98/0.99      | ~ sP0_iProver_split
% 2.98/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 2.98/0.99      | sK0(sK3) = sK1(sK3) ),
% 2.98/0.99      inference(instantiation,[status(thm)],[c_5364]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5125,plain,
% 2.98/0.99      ( sK2 = k1_xboole_0 | sP3_iProver_split = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5120,c_2720]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_17,negated_conjecture,
% 2.98/0.99      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 2.98/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2725,plain,
% 2.98/0.99      ( r2_hidden(sK5,sK2) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3354,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.98/0.99      | v2_funct_1(sK3) != iProver_top
% 2.98/0.99      | sP3_iProver_split != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2725,c_2721]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5127,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.98/0.99      | sP3_iProver_split != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5120,c_3354]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_16,negated_conjecture,
% 2.98/0.99      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 2.98/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2726,plain,
% 2.98/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 2.98/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5131,plain,
% 2.98/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5120,c_2726]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5144,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.98/0.99      | sP3_iProver_split != iProver_top ),
% 2.98/0.99      inference(light_normalisation,[status(thm)],[c_5127,c_5131]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5647,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.98/0.99      | sK2 = k1_xboole_0 ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5125,c_5144]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5126,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.98/0.99      | sP3_iProver_split != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5120,c_3355]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_5648,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.98/0.99      | sK2 = k1_xboole_0 ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5125,c_5126]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6570,plain,
% 2.98/0.99      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_5647,c_5648]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6572,plain,
% 2.98/0.99      ( sK2 = k1_xboole_0 ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_4458,c_20,c_541,c_666,c_791,c_916,c_2283,c_2289,
% 2.98/0.99                 c_2254,c_3043,c_3077,c_3413,c_5122,c_5366,c_6570]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6587,plain,
% 2.98/0.99      ( r2_hidden(sK4,k1_xboole_0) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.98/0.99      inference(demodulation,[status(thm)],[c_6572,c_2724]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6779,plain,
% 2.98/0.99      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_6587,c_23,c_25,c_59,c_62,c_3044,c_3078,c_3193,c_4903,
% 2.98/0.99                 c_4904]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_1,plain,
% 2.98/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.98/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2733,plain,
% 2.98/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_3731,plain,
% 2.98/0.99      ( r2_hidden(X0,X1) = iProver_top
% 2.98/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_2733,c_2734]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6784,plain,
% 2.98/0.99      ( r2_hidden(sK4,X0) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_6779,c_3731]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_11,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.98/0.99      | ~ v1_funct_1(X1)
% 2.98/0.99      | ~ v2_funct_1(X1)
% 2.98/0.99      | ~ v1_relat_1(X1)
% 2.98/0.99      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 2.98/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_283,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.98/0.99      | ~ v2_funct_1(X1)
% 2.98/0.99      | ~ v1_relat_1(X1)
% 2.98/0.99      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 2.98/0.99      | sK3 != X1 ),
% 2.98/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_284,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.98/0.99      | ~ v2_funct_1(sK3)
% 2.98/0.99      | ~ v1_relat_1(sK3)
% 2.98/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 ),
% 2.98/0.99      inference(unflattening,[status(thm)],[c_283]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2257,plain,
% 2.98/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.98/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.98/0.99      | ~ sP2_iProver_split ),
% 2.98/0.99      inference(splitting,
% 2.98/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.98/0.99                [c_284]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2719,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 2.98/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.98/0.99      | sP2_iProver_split != iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2257]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6956,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 2.98/0.99      | sP2_iProver_split != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_6784,c_2719]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2258,plain,
% 2.98/0.99      ( ~ v2_funct_1(sK3) | ~ v1_relat_1(sK3) | sP2_iProver_split ),
% 2.98/0.99      inference(splitting,
% 2.98/0.99                [splitting(split),new_symbols(definition,[])],
% 2.98/0.99                [c_284]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_2300,plain,
% 2.98/0.99      ( v2_funct_1(sK3) != iProver_top
% 2.98/0.99      | v1_relat_1(sK3) != iProver_top
% 2.98/0.99      | sP2_iProver_split = iProver_top ),
% 2.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2258]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7231,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4 ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_6956,c_23,c_25,c_59,c_62,c_2300,c_3044,c_3078,c_3193,
% 2.98/0.99                 c_4903,c_4904]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6586,plain,
% 2.98/0.99      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 2.98/0.99      | v2_funct_1(sK3) != iProver_top ),
% 2.98/0.99      inference(demodulation,[status(thm)],[c_6572,c_2725]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6727,plain,
% 2.98/0.99      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_6586,c_23,c_25,c_59,c_62,c_3044,c_3078,c_3193,c_4903,
% 2.98/0.99                 c_4904]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6732,plain,
% 2.98/0.99      ( r2_hidden(sK5,X0) = iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_6727,c_3731]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6797,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 2.98/0.99      | sP2_iProver_split != iProver_top ),
% 2.98/0.99      inference(superposition,[status(thm)],[c_6732,c_2719]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_6822,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 2.98/0.99      | sP2_iProver_split != iProver_top ),
% 2.98/0.99      inference(light_normalisation,[status(thm)],[c_6797,c_5131]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7129,plain,
% 2.98/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5 ),
% 2.98/0.99      inference(global_propositional_subsumption,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_6822,c_23,c_25,c_59,c_62,c_2300,c_3044,c_3078,c_3193,
% 2.98/0.99                 c_4903,c_4904]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(c_7234,plain,
% 2.98/0.99      ( sK5 = sK4 ),
% 2.98/0.99      inference(demodulation,[status(thm)],[c_7231,c_7129]) ).
% 2.98/0.99  
% 2.98/0.99  cnf(contradiction,plain,
% 2.98/0.99      ( $false ),
% 2.98/0.99      inference(minisat,
% 2.98/0.99                [status(thm)],
% 2.98/0.99                [c_7234,c_5366,c_5122,c_3413,c_3077,c_3043,c_2254,c_2289,
% 2.98/0.99                 c_2283,c_916,c_791,c_666,c_541,c_20]) ).
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/0.99  
% 2.98/0.99  ------                               Statistics
% 2.98/0.99  
% 2.98/0.99  ------ General
% 2.98/0.99  
% 2.98/0.99  abstr_ref_over_cycles:                  0
% 2.98/0.99  abstr_ref_under_cycles:                 0
% 2.98/0.99  gc_basic_clause_elim:                   0
% 2.98/0.99  forced_gc_time:                         0
% 2.98/0.99  parsing_time:                           0.012
% 2.98/0.99  unif_index_cands_time:                  0.
% 2.98/0.99  unif_index_add_time:                    0.
% 2.98/0.99  orderings_time:                         0.
% 2.98/0.99  out_proof_time:                         0.013
% 2.98/0.99  total_time:                             0.207
% 2.98/0.99  num_of_symbols:                         55
% 2.98/0.99  num_of_terms:                           4125
% 2.98/0.99  
% 2.98/0.99  ------ Preprocessing
% 2.98/0.99  
% 2.98/0.99  num_of_splits:                          4
% 2.98/0.99  num_of_split_atoms:                     4
% 2.98/0.99  num_of_reused_defs:                     0
% 2.98/0.99  num_eq_ax_congr_red:                    14
% 2.98/0.99  num_of_sem_filtered_clauses:            1
% 2.98/0.99  num_of_subtypes:                        0
% 2.98/0.99  monotx_restored_types:                  0
% 2.98/0.99  sat_num_of_epr_types:                   0
% 2.98/0.99  sat_num_of_non_cyclic_types:            0
% 2.98/0.99  sat_guarded_non_collapsed_types:        0
% 2.98/0.99  num_pure_diseq_elim:                    0
% 2.98/0.99  simp_replaced_by:                       0
% 2.98/0.99  res_preprocessed:                       123
% 2.98/0.99  prep_upred:                             0
% 2.98/0.99  prep_unflattend:                        10
% 2.98/0.99  smt_new_axioms:                         0
% 2.98/0.99  pred_elim_cands:                        4
% 2.98/0.99  pred_elim:                              2
% 2.98/0.99  pred_elim_cl:                           2
% 2.98/0.99  pred_elim_cycles:                       4
% 2.98/0.99  merged_defs:                            0
% 2.98/0.99  merged_defs_ncl:                        0
% 2.98/0.99  bin_hyper_res:                          0
% 2.98/0.99  prep_cycles:                            4
% 2.98/0.99  pred_elim_time:                         0.028
% 2.98/0.99  splitting_time:                         0.
% 2.98/0.99  sem_filter_time:                        0.
% 2.98/0.99  monotx_time:                            0.
% 2.98/0.99  subtype_inf_time:                       0.
% 2.98/0.99  
% 2.98/0.99  ------ Problem properties
% 2.98/0.99  
% 2.98/0.99  clauses:                                25
% 2.98/0.99  conjectures:                            6
% 2.98/0.99  epr:                                    7
% 2.98/0.99  horn:                                   20
% 2.98/0.99  ground:                                 13
% 2.98/0.99  unary:                                  3
% 2.98/0.99  binary:                                 6
% 2.98/0.99  lits:                                   67
% 2.98/0.99  lits_eq:                                13
% 2.98/0.99  fd_pure:                                0
% 2.98/0.99  fd_pseudo:                              0
% 2.98/0.99  fd_cond:                                0
% 2.98/0.99  fd_pseudo_cond:                         2
% 2.98/0.99  ac_symbols:                             0
% 2.98/0.99  
% 2.98/0.99  ------ Propositional Solver
% 2.98/0.99  
% 2.98/0.99  prop_solver_calls:                      31
% 2.98/0.99  prop_fast_solver_calls:                 1387
% 2.98/0.99  smt_solver_calls:                       0
% 2.98/0.99  smt_fast_solver_calls:                  0
% 2.98/0.99  prop_num_of_clauses:                    1896
% 2.98/0.99  prop_preprocess_simplified:             5677
% 2.98/0.99  prop_fo_subsumed:                       58
% 2.98/0.99  prop_solver_time:                       0.
% 2.98/0.99  smt_solver_time:                        0.
% 2.98/0.99  smt_fast_solver_time:                   0.
% 2.98/0.99  prop_fast_solver_time:                  0.
% 2.98/0.99  prop_unsat_core_time:                   0.
% 2.98/0.99  
% 2.98/0.99  ------ QBF
% 2.98/0.99  
% 2.98/0.99  qbf_q_res:                              0
% 2.98/0.99  qbf_num_tautologies:                    0
% 2.98/0.99  qbf_prep_cycles:                        0
% 2.98/0.99  
% 2.98/0.99  ------ BMC1
% 2.98/0.99  
% 2.98/0.99  bmc1_current_bound:                     -1
% 2.98/0.99  bmc1_last_solved_bound:                 -1
% 2.98/0.99  bmc1_unsat_core_size:                   -1
% 2.98/0.99  bmc1_unsat_core_parents_size:           -1
% 2.98/0.99  bmc1_merge_next_fun:                    0
% 2.98/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.98/0.99  
% 2.98/0.99  ------ Instantiation
% 2.98/0.99  
% 2.98/0.99  inst_num_of_clauses:                    566
% 2.98/0.99  inst_num_in_passive:                    109
% 2.98/0.99  inst_num_in_active:                     427
% 2.98/0.99  inst_num_in_unprocessed:                31
% 2.98/0.99  inst_num_of_loops:                      470
% 2.98/0.99  inst_num_of_learning_restarts:          0
% 2.98/0.99  inst_num_moves_active_passive:          36
% 2.98/0.99  inst_lit_activity:                      0
% 2.98/0.99  inst_lit_activity_moves:                0
% 2.98/0.99  inst_num_tautologies:                   0
% 2.98/0.99  inst_num_prop_implied:                  0
% 2.98/0.99  inst_num_existing_simplified:           0
% 2.98/0.99  inst_num_eq_res_simplified:             0
% 2.98/0.99  inst_num_child_elim:                    0
% 2.98/0.99  inst_num_of_dismatching_blockings:      248
% 2.98/0.99  inst_num_of_non_proper_insts:           770
% 2.98/0.99  inst_num_of_duplicates:                 0
% 2.98/0.99  inst_inst_num_from_inst_to_res:         0
% 2.98/0.99  inst_dismatching_checking_time:         0.
% 2.98/0.99  
% 2.98/0.99  ------ Resolution
% 2.98/0.99  
% 2.98/0.99  res_num_of_clauses:                     0
% 2.98/0.99  res_num_in_passive:                     0
% 2.98/0.99  res_num_in_active:                      0
% 2.98/0.99  res_num_of_loops:                       127
% 2.98/0.99  res_forward_subset_subsumed:            93
% 2.98/0.99  res_backward_subset_subsumed:           6
% 2.98/0.99  res_forward_subsumed:                   0
% 2.98/0.99  res_backward_subsumed:                  0
% 2.98/0.99  res_forward_subsumption_resolution:     0
% 2.98/0.99  res_backward_subsumption_resolution:    0
% 2.98/0.99  res_clause_to_clause_subsumption:       259
% 2.98/0.99  res_orphan_elimination:                 0
% 2.98/0.99  res_tautology_del:                      131
% 2.98/0.99  res_num_eq_res_simplified:              0
% 2.98/0.99  res_num_sel_changes:                    0
% 2.98/0.99  res_moves_from_active_to_pass:          0
% 2.98/0.99  
% 2.98/0.99  ------ Superposition
% 2.98/0.99  
% 2.98/0.99  sup_time_total:                         0.
% 2.98/0.99  sup_time_generating:                    0.
% 2.98/0.99  sup_time_sim_full:                      0.
% 2.98/0.99  sup_time_sim_immed:                     0.
% 2.98/0.99  
% 2.98/0.99  sup_num_of_clauses:                     104
% 2.98/0.99  sup_num_in_active:                      63
% 2.98/0.99  sup_num_in_passive:                     41
% 2.98/0.99  sup_num_of_loops:                       92
% 2.98/0.99  sup_fw_superposition:                   66
% 2.98/0.99  sup_bw_superposition:                   100
% 2.98/0.99  sup_immediate_simplified:               53
% 2.98/0.99  sup_given_eliminated:                   2
% 2.98/0.99  comparisons_done:                       0
% 2.98/0.99  comparisons_avoided:                    15
% 2.98/0.99  
% 2.98/0.99  ------ Simplifications
% 2.98/0.99  
% 2.98/0.99  
% 2.98/0.99  sim_fw_subset_subsumed:                 8
% 2.98/0.99  sim_bw_subset_subsumed:                 9
% 2.98/0.99  sim_fw_subsumed:                        4
% 2.98/0.99  sim_bw_subsumed:                        5
% 2.98/0.99  sim_fw_subsumption_res:                 1
% 2.98/0.99  sim_bw_subsumption_res:                 0
% 2.98/0.99  sim_tautology_del:                      1
% 2.98/0.99  sim_eq_tautology_del:                   10
% 2.98/0.99  sim_eq_res_simp:                        0
% 2.98/0.99  sim_fw_demodulated:                     16
% 2.98/0.99  sim_bw_demodulated:                     39
% 2.98/0.99  sim_light_normalised:                   9
% 2.98/0.99  sim_joinable_taut:                      0
% 2.98/0.99  sim_joinable_simp:                      0
% 2.98/0.99  sim_ac_normalised:                      0
% 2.98/0.99  sim_smt_subsumption:                    0
% 2.98/0.99  
%------------------------------------------------------------------------------
