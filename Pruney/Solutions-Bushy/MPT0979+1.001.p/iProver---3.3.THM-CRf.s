%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:33 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  202 (182805 expanded)
%              Number of clauses        :  158 (55652 expanded)
%              Number of leaves         :   12 (36543 expanded)
%              Depth                    :   43
%              Number of atoms          :  799 (1582834 expanded)
%              Number of equality atoms :  485 (646194 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v2_funct_1(X2)
          <=> ! [X3,X4] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  & r2_hidden(X4,X0)
                  & r2_hidden(X3,X0) )
               => X3 = X4 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X5,X6] :
            ( X5 = X6
            | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
            | ~ r2_hidden(X6,X0)
            | ~ r2_hidden(X5,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f21])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ? [X3,X4] :
          ( X3 != X4
          & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
          & r2_hidden(X4,X0)
          & r2_hidden(X3,X0) )
     => ( sK5 != sK6
        & k1_funct_1(X2,sK5) = k1_funct_1(X2,sK6)
        & r2_hidden(sK6,X0)
        & r2_hidden(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) )
          | ~ v2_funct_1(X2) )
        & ( ! [X5,X6] :
              ( X5 = X6
              | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
              | ~ r2_hidden(X6,X0)
              | ~ r2_hidden(X5,X0) )
          | v2_funct_1(X2) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ? [X4,X3] :
            ( X3 != X4
            & k1_funct_1(sK4,X3) = k1_funct_1(sK4,X4)
            & r2_hidden(X4,sK2)
            & r2_hidden(X3,sK2) )
        | ~ v2_funct_1(sK4) )
      & ( ! [X6,X5] :
            ( X5 = X6
            | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6)
            | ~ r2_hidden(X6,sK2)
            | ~ r2_hidden(X5,sK2) )
        | v2_funct_1(sK4) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ( ( sK5 != sK6
        & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
        & r2_hidden(sK6,sK2)
        & r2_hidden(sK5,sK2) )
      | ~ v2_funct_1(sK4) )
    & ( ! [X5,X6] :
          ( X5 = X6
          | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6)
          | ~ r2_hidden(X6,sK2)
          | ~ r2_hidden(X5,sK2) )
      | v2_funct_1(sK4) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f22,f24,f23])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
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

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X6,X5] :
      ( X5 = X6
      | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK2)
      | v2_funct_1(sK4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,
    ( sK5 != sK6
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f28])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_441,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_442,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1801,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_2081,plain,
    ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_1864,plain,
    ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_1817,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2211,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_281,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_282,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_1805,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_282])).

cnf(c_2213,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_2214,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_2471,plain,
    ( v2_funct_1(sK4) = iProver_top
    | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2081,c_1864,c_2211,c_2214])).

cnf(c_2472,plain,
    ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v2_funct_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2471])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1809,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2074,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1809])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_245,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_246,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_595,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK3 != X1
    | sK2 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_246])).

cnf(c_596,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_1157,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_596])).

cnf(c_1797,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_1157])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_236,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_237,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_1806,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_relset_1(X0_47,X1_47,sK4) = k1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_237])).

cnf(c_2232,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_1806])).

cnf(c_2319,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1797,c_2232])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_428,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_429,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_1802,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_2080,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_430,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_2464,plain,
    ( v2_funct_1(sK4) = iProver_top
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2080,c_430,c_2211,c_2214])).

cnf(c_2465,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2464])).

cnf(c_2628,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK2) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_2465])).

cnf(c_14,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1811,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2072,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_2478,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2472,c_2072])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1808,negated_conjecture,
    ( ~ r2_hidden(X0_50,sK2)
    | ~ r2_hidden(X1_50,sK2)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,X1_50) != k1_funct_1(sK4,X0_50)
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2075,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | r2_hidden(X0_50,sK2) != iProver_top
    | r2_hidden(X1_50,sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1808])).

cnf(c_2524,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = X0_50
    | r2_hidden(X0_50,sK2) != iProver_top
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2075])).

cnf(c_2563,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2524])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_454,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_455,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK1(sK4) != sK0(sK4) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_1800,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK1(sK4) != sK0(sK4) ),
    inference(subtyping,[status(esa)],[c_455])).

cnf(c_1865,plain,
    ( sK1(sK4) != sK0(sK4)
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_2508,plain,
    ( ~ r2_hidden(sK1(sK4),sK2)
    | ~ r2_hidden(sK0(sK4),sK2)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
    | sK1(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_2509,plain,
    ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2508])).

cnf(c_2645,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2563,c_1865,c_2211,c_2214,c_2478,c_2509])).

cnf(c_2811,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK3 = k1_xboole_0
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2628,c_2645])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_391,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_392,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | X0 = X1
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_1804,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK4))
    | ~ r2_hidden(X1_50,k1_relat_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50 ),
    inference(subtyping,[status(esa)],[c_392])).

cnf(c_1814,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1804])).

cnf(c_2077,plain,
    ( v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_1860,plain,
    ( v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1814])).

cnf(c_2361,plain,
    ( v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2077,c_1860,c_2211,c_2214])).

cnf(c_10,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_415,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_416,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_1803,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_2079,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1803])).

cnf(c_417,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_2424,plain,
    ( v2_funct_1(sK4) = iProver_top
    | r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2079,c_417,c_2211,c_2214])).

cnf(c_2425,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2424])).

cnf(c_2629,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK4),sK2) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_2425])).

cnf(c_1813,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK4))
    | ~ r2_hidden(X1_50,k1_relat_1(sK4))
    | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1804])).

cnf(c_2078,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X1_50,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1813])).

cnf(c_2523,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = X0_50
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_2078])).

cnf(c_2726,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2523])).

cnf(c_2744,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2465,c_2726])).

cnf(c_2840,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | v2_funct_1(sK4) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2744,c_417,c_430,c_1865,c_2211,c_2214,c_2726])).

cnf(c_2848,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2840,c_2072])).

cnf(c_2921,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2811,c_2361,c_2629,c_2848])).

cnf(c_2928,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,sK5)
    | sK6 = X0_50
    | sK3 = k1_xboole_0
    | r2_hidden(X0_50,sK2) != iProver_top
    | r2_hidden(sK6,sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2921,c_2075])).

cnf(c_28,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1819,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1849,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_13,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1812,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1851,plain,
    ( sK5 != sK6
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_1852,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_2270,plain,
    ( ~ r2_hidden(sK6,k1_relat_1(sK4))
    | ~ r2_hidden(sK5,k1_relat_1(sK4))
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_2271,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK5 = sK6
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2270])).

cnf(c_1834,plain,
    ( ~ r2_hidden(X0_50,X0_47)
    | r2_hidden(X1_50,X1_47)
    | X1_50 != X0_50
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_2257,plain,
    ( r2_hidden(X0_50,X0_47)
    | ~ r2_hidden(sK6,sK2)
    | X0_50 != sK6
    | X0_47 != sK2 ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_2312,plain,
    ( r2_hidden(sK6,k1_relat_1(sK4))
    | ~ r2_hidden(sK6,sK2)
    | sK6 != sK6
    | k1_relat_1(sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_2313,plain,
    ( sK6 != sK6
    | k1_relat_1(sK4) != sK2
    | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK6,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2312])).

cnf(c_2396,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_2252,plain,
    ( r2_hidden(X0_50,X0_47)
    | ~ r2_hidden(sK5,sK2)
    | X0_50 != sK5
    | X0_47 != sK2 ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_2860,plain,
    ( r2_hidden(sK5,k1_relat_1(sK4))
    | ~ r2_hidden(sK5,sK2)
    | sK5 != sK5
    | k1_relat_1(sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_2861,plain,
    ( sK5 != sK5
    | k1_relat_1(sK4) != sK2
    | r2_hidden(sK5,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2860])).

cnf(c_3011,plain,
    ( r2_hidden(sK6,sK2) != iProver_top
    | r2_hidden(X0_50,sK2) != iProver_top
    | sK3 = k1_xboole_0
    | sK6 = X0_50
    | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2928,c_28,c_1849,c_1851,c_1852,c_1860,c_2211,c_2214,c_2271,c_2313,c_2319,c_2396,c_2861])).

cnf(c_3012,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,sK5)
    | sK6 = X0_50
    | sK3 = k1_xboole_0
    | r2_hidden(X0_50,sK2) != iProver_top
    | r2_hidden(sK6,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3011])).

cnf(c_3024,plain,
    ( sK6 = sK5
    | sK3 = k1_xboole_0
    | r2_hidden(sK6,sK2) != iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3012])).

cnf(c_3045,plain,
    ( sK6 = sK5
    | sK3 = k1_xboole_0
    | r2_hidden(sK6,sK2) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2074,c_3024])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1823,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_2265,plain,
    ( sK6 != X0_50
    | sK5 != X0_50
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_2266,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2265])).

cnf(c_3070,plain,
    ( sK3 = k1_xboole_0
    | v2_funct_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3045,c_28,c_29,c_1849,c_1851,c_2266,c_3024])).

cnf(c_3076,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2472,c_3070])).

cnf(c_3077,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3076,c_1865,c_2211,c_2214,c_2509,c_2628,c_2629,c_3070])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1807,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3087,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3077,c_1807])).

cnf(c_3088,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3087])).

cnf(c_3126,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3088,c_2074])).

cnf(c_2296,plain,
    ( ~ r2_hidden(X0_50,k1_relat_1(sK4))
    | ~ r2_hidden(sK6,k1_relat_1(sK4))
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,sK6) != k1_funct_1(sK4,X0_50)
    | sK6 = X0_50 ),
    inference(instantiation,[status(thm)],[c_1813])).

cnf(c_2297,plain,
    ( k1_funct_1(sK4,sK6) != k1_funct_1(sK4,X0_50)
    | sK6 = X0_50
    | r2_hidden(X0_50,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2296])).

cnf(c_2299,plain,
    ( k1_funct_1(sK4,sK6) != k1_funct_1(sK4,sK5)
    | sK6 = sK5
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_2297])).

cnf(c_2378,plain,
    ( ~ r2_hidden(X0_50,X0_47)
    | r2_hidden(sK6,k1_relat_1(sK4))
    | sK6 != X0_50
    | k1_relat_1(sK4) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_2488,plain,
    ( ~ r2_hidden(sK6,X0_47)
    | r2_hidden(sK6,k1_relat_1(sK4))
    | sK6 != sK6
    | k1_relat_1(sK4) != X0_47 ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_2490,plain,
    ( sK6 != sK6
    | k1_relat_1(sK4) != X0_47
    | r2_hidden(sK6,X0_47) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2488])).

cnf(c_2492,plain,
    ( sK6 != sK6
    | k1_relat_1(sK4) != k1_xboole_0
    | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2490])).

cnf(c_2865,plain,
    ( ~ r2_hidden(X0_50,X0_47)
    | r2_hidden(sK5,k1_relat_1(sK4))
    | sK5 != X0_50
    | k1_relat_1(sK4) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_2866,plain,
    ( sK5 != X0_50
    | k1_relat_1(sK4) != X0_47
    | r2_hidden(X0_50,X0_47) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_2868,plain,
    ( sK5 != sK5
    | k1_relat_1(sK4) != k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2866])).

cnf(c_3082,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_3077,c_2232])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_328,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_329,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_620,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK3 != X0
    | sK2 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_329])).

cnf(c_621,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_1798,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_621])).

cnf(c_3085,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3077,c_1798])).

cnf(c_3096,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3085,c_3088])).

cnf(c_3097,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3096])).

cnf(c_3101,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3082,c_3088,c_3097])).

cnf(c_1810,negated_conjecture,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2073,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1810])).

cnf(c_3127,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3088,c_2073])).

cnf(c_3174,plain,
    ( v2_funct_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3126,c_1849,c_1851,c_1860,c_2211,c_2214,c_2266,c_2299,c_2396,c_2492,c_2848,c_2868,c_3101,c_3127])).

cnf(c_3179,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4)) ),
    inference(superposition,[status(thm)],[c_2472,c_3174])).

cnf(c_3125,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3088,c_2075])).

cnf(c_3224,plain,
    ( r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top
    | X0_50 = X1_50
    | k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3125,c_1849,c_1851,c_1860,c_2211,c_2214,c_2266,c_2299,c_2396,c_2492,c_2848,c_2868,c_3101,c_3126,c_3127])).

cnf(c_3225,plain,
    ( k1_funct_1(sK4,X0_50) != k1_funct_1(sK4,X1_50)
    | X0_50 = X1_50
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(X1_50,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3224])).

cnf(c_3293,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50)
    | sK1(sK4) = X0_50
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3179,c_3225])).

cnf(c_3238,plain,
    ( r2_hidden(sK1(sK4),k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3101,c_2465])).

cnf(c_3299,plain,
    ( r2_hidden(X0_50,k1_xboole_0) != iProver_top
    | sK1(sK4) = X0_50
    | k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3293,c_1849,c_1851,c_1860,c_2211,c_2214,c_2266,c_2299,c_2396,c_2492,c_2848,c_2868,c_3101,c_3126,c_3127,c_3238])).

cnf(c_3300,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_50)
    | sK1(sK4) = X0_50
    | r2_hidden(X0_50,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3299])).

cnf(c_3309,plain,
    ( sK1(sK4) = sK0(sK4)
    | r2_hidden(sK0(sK4),k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3300])).

cnf(c_3239,plain,
    ( r2_hidden(sK0(sK4),k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3101,c_2425])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3309,c_3239,c_3174,c_2214,c_2211,c_1865])).


%------------------------------------------------------------------------------
