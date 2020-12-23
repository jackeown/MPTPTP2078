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
% DateTime   : Thu Dec  3 12:01:36 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  199 (208760 expanded)
%              Number of clauses        :  153 (66221 expanded)
%              Number of leaves         :   13 (41442 expanded)
%              Depth                    :   38
%              Number of atoms          :  762 (1765199 expanded)
%              Number of equality atoms :  439 (714248 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(flattening,[],[f9])).

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
    inference(nnf_transformation,[],[f10])).

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

fof(f32,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

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
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f15])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f26,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f25,f24])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f42,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,
    ( sK5 != sK6
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X6,X5] :
      ( X5 = X6
      | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X5,sK2)
      | v2_funct_1(sK4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_454,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_22])).

cnf(c_455,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_1635,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
    inference(subtyping,[status(esa)],[c_455])).

cnf(c_1927,plain,
    ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_1698,plain,
    ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_1652,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2068,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_245,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_246,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_1640,plain,
    ( ~ v1_relat_1(X0_47)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_2063,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_47,X1_47))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_2109,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_2110,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2109])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1647,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2132,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_2133,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2132])).

cnf(c_2399,plain,
    ( v2_funct_1(sK4) = iProver_top
    | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1927,c_1698,c_2068,c_2110,c_2133])).

cnf(c_2400,plain,
    ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
    | v2_funct_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2399])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_260,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_261,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_511,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK3 != X1
    | sK2 != X0
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_261])).

cnf(c_512,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_1074,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_512])).

cnf(c_1631,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_1074])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_296,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_297,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_1639,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_relset_1(X0_47,X1_47,sK4) = k1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_297])).

cnf(c_2091,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_1639])).

cnf(c_2195,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1631,c_2091])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_441,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_442,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1636,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_1926,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(c_443,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_2355,plain,
    ( v2_funct_1(sK4) = iProver_top
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1926,c_443,c_2068,c_2110,c_2133])).

cnf(c_2356,plain,
    ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2355])).

cnf(c_2524,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK2) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_2356])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_30,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_428,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_429,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_430,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_1653,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_1682,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_14,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1646,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | sK5 != sK6 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1685,plain,
    ( sK5 != sK6
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_15,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1645,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1686,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_404,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_405,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_1638,plain,
    ( ~ r2_hidden(X0_49,k1_relat_1(sK4))
    | ~ r2_hidden(X1_49,k1_relat_1(sK4))
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
    | X1_49 = X0_49 ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_1649,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1638])).

cnf(c_1694,plain,
    ( v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1649])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_467,plain,
    ( v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_22])).

cnf(c_468,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK1(sK4) != sK0(sK4) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_1634,plain,
    ( v2_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | sK1(sK4) != sK0(sK4) ),
    inference(subtyping,[status(esa)],[c_468])).

cnf(c_1699,plain,
    ( sK1(sK4) != sK0(sK4)
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_1657,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_2254,plain,
    ( sK6 != X0_49
    | sK5 != X0_49
    | sK5 = sK6 ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_2255,plain,
    ( sK6 != sK5
    | sK5 = sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2254])).

cnf(c_1648,plain,
    ( ~ r2_hidden(X0_49,k1_relat_1(sK4))
    | ~ r2_hidden(X1_49,k1_relat_1(sK4))
    | k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
    | X1_49 = X0_49
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1638])).

cnf(c_2366,plain,
    ( ~ r2_hidden(X0_49,k1_relat_1(sK4))
    | ~ r2_hidden(sK6,k1_relat_1(sK4))
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,sK6)
    | sK6 = X0_49 ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_2372,plain,
    ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,sK6)
    | sK6 = X0_49
    | r2_hidden(X0_49,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_2374,plain,
    ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
    | sK6 = sK5
    | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_1667,plain,
    ( ~ r2_hidden(X0_49,X0_47)
    | r2_hidden(X1_49,X1_47)
    | X1_49 != X0_49
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_2227,plain,
    ( r2_hidden(X0_49,X0_47)
    | ~ r2_hidden(sK5,sK2)
    | X0_49 != sK5
    | X0_47 != sK2 ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_2378,plain,
    ( r2_hidden(sK5,k1_relat_1(sK4))
    | ~ r2_hidden(sK5,sK2)
    | sK5 != sK5
    | k1_relat_1(sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_2227])).

cnf(c_2379,plain,
    ( sK5 != sK5
    | k1_relat_1(sK4) != sK2
    | r2_hidden(sK5,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK5,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2378])).

cnf(c_1923,plain,
    ( v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1649])).

cnf(c_2238,plain,
    ( v2_funct_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1923,c_1694,c_2068,c_2110,c_2133])).

cnf(c_2405,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2400,c_2238])).

cnf(c_1637,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_1925,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1637])).

cnf(c_2348,plain,
    ( v2_funct_1(sK4) = iProver_top
    | r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1925,c_430,c_2068,c_2110,c_2133])).

cnf(c_2349,plain,
    ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_2348])).

cnf(c_2525,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK0(sK4),sK2) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_2349])).

cnf(c_2232,plain,
    ( r2_hidden(X0_49,X0_47)
    | ~ r2_hidden(sK6,sK2)
    | X0_49 != sK6
    | X0_47 != sK2 ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_2593,plain,
    ( r2_hidden(sK6,k1_relat_1(sK4))
    | ~ r2_hidden(sK6,sK2)
    | sK6 != sK6
    | k1_relat_1(sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_2232])).

cnf(c_2597,plain,
    ( sK6 != sK6
    | k1_relat_1(sK4) != sK2
    | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top
    | r2_hidden(sK6,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2593])).

cnf(c_2639,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK4)
    | X1 = X0
    | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1642,negated_conjecture,
    ( ~ r2_hidden(X0_49,sK2)
    | ~ r2_hidden(X1_49,sK2)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,X1_49) != k1_funct_1(sK4,X0_49)
    | X1_49 = X0_49 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2803,plain,
    ( ~ r2_hidden(sK1(sK4),sK2)
    | ~ r2_hidden(sK0(sK4),sK2)
    | v2_funct_1(sK4)
    | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
    | sK1(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_2804,plain,
    ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2803])).

cnf(c_2802,plain,
    ( ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
    | ~ r2_hidden(sK0(sK4),k1_relat_1(sK4))
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,sK1(sK4))
    | sK1(sK4) = sK0(sK4) ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_2806,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,sK1(sK4))
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2802])).

cnf(c_2811,plain,
    ( sK3 = k1_xboole_0
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_29,c_30,c_430,c_443,c_1682,c_1685,c_1686,c_1694,c_1698,c_1699,c_2068,c_2110,c_2133,c_2195,c_2255,c_2374,c_2379,c_2405,c_2525,c_2597,c_2639,c_2804,c_2806])).

cnf(c_2815,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2811,c_29,c_30,c_430,c_443,c_1682,c_1685,c_1686,c_1694,c_1698,c_1699,c_2068,c_2110,c_2133,c_2195,c_2255,c_2374,c_2379,c_2405,c_2524,c_2525,c_2597,c_2639,c_2804,c_2806])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1641,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2823,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2815,c_1641])).

cnf(c_2824,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2823])).

cnf(c_1643,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1920,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1643])).

cnf(c_2850,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2824,c_1920])).

cnf(c_1918,plain,
    ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1645])).

cnf(c_2406,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2400,c_1918])).

cnf(c_1921,plain,
    ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X0_49,sK2) != iProver_top
    | r2_hidden(X1_49,sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_2421,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_49)
    | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = X0_49
    | r2_hidden(X0_49,sK2) != iProver_top
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2406,c_1921])).

cnf(c_2548,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | sK1(sK4) = sK0(sK4)
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2421])).

cnf(c_2608,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | r2_hidden(sK1(sK4),sK2) != iProver_top
    | r2_hidden(sK0(sK4),sK2) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2548,c_1699,c_2068,c_2110,c_2133])).

cnf(c_2846,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK4),k1_xboole_0) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2824,c_2608])).

cnf(c_2818,plain,
    ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2815,c_2091])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_340,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_341,plain,
    ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_536,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK3 != X0
    | sK2 != k1_xboole_0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_341])).

cnf(c_537,plain,
    ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_1632,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_537])).

cnf(c_2821,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2815,c_1632])).

cnf(c_2832,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2821,c_2824])).

cnf(c_2833,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2832])).

cnf(c_2837,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2818,c_2824,c_2833])).

cnf(c_3032,plain,
    ( r2_hidden(sK1(sK4),k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2837,c_2356])).

cnf(c_3033,plain,
    ( r2_hidden(sK0(sK4),k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2837,c_2349])).

cnf(c_3170,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
    | v2_funct_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2846,c_3032,c_3033])).

cnf(c_3177,plain,
    ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3170,c_1918])).

cnf(c_1924,plain,
    ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
    | X1_49 = X0_49
    | r2_hidden(X1_49,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0_49,k1_relat_1(sK4)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_3034,plain,
    ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X1_49,k1_xboole_0) != iProver_top
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_2837,c_1924])).

cnf(c_2849,plain,
    ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X1_49,k1_xboole_0) != iProver_top
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | v2_funct_1(sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2824,c_1921])).

cnf(c_3243,plain,
    ( r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | r2_hidden(X1_49,k1_xboole_0) != iProver_top
    | X0_49 = X1_49
    | k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3034,c_2238,c_2849])).

cnf(c_3244,plain,
    ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | r2_hidden(X1_49,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3243])).

cnf(c_3253,plain,
    ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,sK5)
    | sK6 = X0_49
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3177,c_3244])).

cnf(c_3387,plain,
    ( sK6 = sK5
    | r2_hidden(sK6,k1_xboole_0) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3253])).

cnf(c_3634,plain,
    ( sK6 = sK5
    | r2_hidden(sK6,k1_xboole_0) != iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_3387])).

cnf(c_1644,negated_conjecture,
    ( r2_hidden(sK6,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1919,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_2851,plain,
    ( r2_hidden(sK6,k1_xboole_0) = iProver_top
    | v2_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2824,c_1919])).

cnf(c_3799,plain,
    ( v2_funct_1(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3634,c_1682,c_1685,c_2255,c_2850,c_2851,c_3387])).

cnf(c_3804,plain,
    ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4)) ),
    inference(superposition,[status(thm)],[c_2400,c_3799])).

cnf(c_3811,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_49)
    | sK1(sK4) = X0_49
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3804,c_3244])).

cnf(c_3396,plain,
    ( r2_hidden(sK1(sK4),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3032,c_1682,c_1685,c_2255,c_2850,c_2851,c_3387])).

cnf(c_3915,plain,
    ( r2_hidden(X0_49,k1_xboole_0) != iProver_top
    | sK1(sK4) = X0_49
    | k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3811,c_1682,c_1685,c_2255,c_2850,c_2851,c_3032,c_3387])).

cnf(c_3916,plain,
    ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_49)
    | sK1(sK4) = X0_49
    | r2_hidden(X0_49,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3915])).

cnf(c_3925,plain,
    ( sK1(sK4) = sK0(sK4)
    | r2_hidden(sK0(sK4),k1_xboole_0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3916])).

cnf(c_3541,plain,
    ( r2_hidden(sK0(sK4),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3033,c_1682,c_1685,c_2255,c_2850,c_2851,c_3387])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3925,c_3799,c_3541,c_2133,c_2110,c_2068,c_1699])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:12:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.81/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.81/0.98  
% 1.81/0.98  ------  iProver source info
% 1.81/0.98  
% 1.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.81/0.98  git: non_committed_changes: false
% 1.81/0.98  git: last_make_outside_of_git: false
% 1.81/0.98  
% 1.81/0.98  ------ 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options
% 1.81/0.98  
% 1.81/0.98  --out_options                           all
% 1.81/0.98  --tptp_safe_out                         true
% 1.81/0.98  --problem_path                          ""
% 1.81/0.98  --include_path                          ""
% 1.81/0.98  --clausifier                            res/vclausify_rel
% 1.81/0.98  --clausifier_options                    --mode clausify
% 1.81/0.98  --stdin                                 false
% 1.81/0.98  --stats_out                             all
% 1.81/0.98  
% 1.81/0.98  ------ General Options
% 1.81/0.98  
% 1.81/0.98  --fof                                   false
% 1.81/0.98  --time_out_real                         305.
% 1.81/0.98  --time_out_virtual                      -1.
% 1.81/0.98  --symbol_type_check                     false
% 1.81/0.98  --clausify_out                          false
% 1.81/0.98  --sig_cnt_out                           false
% 1.81/0.98  --trig_cnt_out                          false
% 1.81/0.98  --trig_cnt_out_tolerance                1.
% 1.81/0.98  --trig_cnt_out_sk_spl                   false
% 1.81/0.98  --abstr_cl_out                          false
% 1.81/0.98  
% 1.81/0.98  ------ Global Options
% 1.81/0.98  
% 1.81/0.98  --schedule                              default
% 1.81/0.98  --add_important_lit                     false
% 1.81/0.98  --prop_solver_per_cl                    1000
% 1.81/0.98  --min_unsat_core                        false
% 1.81/0.98  --soft_assumptions                      false
% 1.81/0.98  --soft_lemma_size                       3
% 1.81/0.98  --prop_impl_unit_size                   0
% 1.81/0.98  --prop_impl_unit                        []
% 1.81/0.98  --share_sel_clauses                     true
% 1.81/0.98  --reset_solvers                         false
% 1.81/0.98  --bc_imp_inh                            [conj_cone]
% 1.81/0.98  --conj_cone_tolerance                   3.
% 1.81/0.98  --extra_neg_conj                        none
% 1.81/0.98  --large_theory_mode                     true
% 1.81/0.98  --prolific_symb_bound                   200
% 1.81/0.98  --lt_threshold                          2000
% 1.81/0.98  --clause_weak_htbl                      true
% 1.81/0.98  --gc_record_bc_elim                     false
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing Options
% 1.81/0.98  
% 1.81/0.98  --preprocessing_flag                    true
% 1.81/0.98  --time_out_prep_mult                    0.1
% 1.81/0.98  --splitting_mode                        input
% 1.81/0.98  --splitting_grd                         true
% 1.81/0.98  --splitting_cvd                         false
% 1.81/0.98  --splitting_cvd_svl                     false
% 1.81/0.98  --splitting_nvd                         32
% 1.81/0.98  --sub_typing                            true
% 1.81/0.98  --prep_gs_sim                           true
% 1.81/0.98  --prep_unflatten                        true
% 1.81/0.98  --prep_res_sim                          true
% 1.81/0.98  --prep_upred                            true
% 1.81/0.98  --prep_sem_filter                       exhaustive
% 1.81/0.98  --prep_sem_filter_out                   false
% 1.81/0.98  --pred_elim                             true
% 1.81/0.98  --res_sim_input                         true
% 1.81/0.98  --eq_ax_congr_red                       true
% 1.81/0.98  --pure_diseq_elim                       true
% 1.81/0.98  --brand_transform                       false
% 1.81/0.98  --non_eq_to_eq                          false
% 1.81/0.98  --prep_def_merge                        true
% 1.81/0.98  --prep_def_merge_prop_impl              false
% 1.81/0.98  --prep_def_merge_mbd                    true
% 1.81/0.98  --prep_def_merge_tr_red                 false
% 1.81/0.98  --prep_def_merge_tr_cl                  false
% 1.81/0.98  --smt_preprocessing                     true
% 1.81/0.98  --smt_ac_axioms                         fast
% 1.81/0.98  --preprocessed_out                      false
% 1.81/0.98  --preprocessed_stats                    false
% 1.81/0.98  
% 1.81/0.98  ------ Abstraction refinement Options
% 1.81/0.98  
% 1.81/0.98  --abstr_ref                             []
% 1.81/0.98  --abstr_ref_prep                        false
% 1.81/0.98  --abstr_ref_until_sat                   false
% 1.81/0.98  --abstr_ref_sig_restrict                funpre
% 1.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/0.98  --abstr_ref_under                       []
% 1.81/0.98  
% 1.81/0.98  ------ SAT Options
% 1.81/0.98  
% 1.81/0.98  --sat_mode                              false
% 1.81/0.98  --sat_fm_restart_options                ""
% 1.81/0.98  --sat_gr_def                            false
% 1.81/0.98  --sat_epr_types                         true
% 1.81/0.98  --sat_non_cyclic_types                  false
% 1.81/0.98  --sat_finite_models                     false
% 1.81/0.98  --sat_fm_lemmas                         false
% 1.81/0.98  --sat_fm_prep                           false
% 1.81/0.98  --sat_fm_uc_incr                        true
% 1.81/0.98  --sat_out_model                         small
% 1.81/0.98  --sat_out_clauses                       false
% 1.81/0.98  
% 1.81/0.98  ------ QBF Options
% 1.81/0.98  
% 1.81/0.98  --qbf_mode                              false
% 1.81/0.98  --qbf_elim_univ                         false
% 1.81/0.98  --qbf_dom_inst                          none
% 1.81/0.98  --qbf_dom_pre_inst                      false
% 1.81/0.98  --qbf_sk_in                             false
% 1.81/0.98  --qbf_pred_elim                         true
% 1.81/0.98  --qbf_split                             512
% 1.81/0.98  
% 1.81/0.98  ------ BMC1 Options
% 1.81/0.98  
% 1.81/0.98  --bmc1_incremental                      false
% 1.81/0.98  --bmc1_axioms                           reachable_all
% 1.81/0.98  --bmc1_min_bound                        0
% 1.81/0.98  --bmc1_max_bound                        -1
% 1.81/0.98  --bmc1_max_bound_default                -1
% 1.81/0.98  --bmc1_symbol_reachability              true
% 1.81/0.98  --bmc1_property_lemmas                  false
% 1.81/0.98  --bmc1_k_induction                      false
% 1.81/0.98  --bmc1_non_equiv_states                 false
% 1.81/0.98  --bmc1_deadlock                         false
% 1.81/0.98  --bmc1_ucm                              false
% 1.81/0.98  --bmc1_add_unsat_core                   none
% 1.81/0.98  --bmc1_unsat_core_children              false
% 1.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/0.98  --bmc1_out_stat                         full
% 1.81/0.98  --bmc1_ground_init                      false
% 1.81/0.98  --bmc1_pre_inst_next_state              false
% 1.81/0.98  --bmc1_pre_inst_state                   false
% 1.81/0.98  --bmc1_pre_inst_reach_state             false
% 1.81/0.98  --bmc1_out_unsat_core                   false
% 1.81/0.98  --bmc1_aig_witness_out                  false
% 1.81/0.98  --bmc1_verbose                          false
% 1.81/0.98  --bmc1_dump_clauses_tptp                false
% 1.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.81/0.98  --bmc1_dump_file                        -
% 1.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.81/0.98  --bmc1_ucm_extend_mode                  1
% 1.81/0.98  --bmc1_ucm_init_mode                    2
% 1.81/0.98  --bmc1_ucm_cone_mode                    none
% 1.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.81/0.98  --bmc1_ucm_relax_model                  4
% 1.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/0.98  --bmc1_ucm_layered_model                none
% 1.81/0.98  --bmc1_ucm_max_lemma_size               10
% 1.81/0.98  
% 1.81/0.98  ------ AIG Options
% 1.81/0.98  
% 1.81/0.98  --aig_mode                              false
% 1.81/0.98  
% 1.81/0.98  ------ Instantiation Options
% 1.81/0.98  
% 1.81/0.98  --instantiation_flag                    true
% 1.81/0.98  --inst_sos_flag                         false
% 1.81/0.98  --inst_sos_phase                        true
% 1.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel_side                     num_symb
% 1.81/0.98  --inst_solver_per_active                1400
% 1.81/0.98  --inst_solver_calls_frac                1.
% 1.81/0.98  --inst_passive_queue_type               priority_queues
% 1.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/0.98  --inst_passive_queues_freq              [25;2]
% 1.81/0.98  --inst_dismatching                      true
% 1.81/0.98  --inst_eager_unprocessed_to_passive     true
% 1.81/0.98  --inst_prop_sim_given                   true
% 1.81/0.98  --inst_prop_sim_new                     false
% 1.81/0.98  --inst_subs_new                         false
% 1.81/0.98  --inst_eq_res_simp                      false
% 1.81/0.98  --inst_subs_given                       false
% 1.81/0.98  --inst_orphan_elimination               true
% 1.81/0.98  --inst_learning_loop_flag               true
% 1.81/0.98  --inst_learning_start                   3000
% 1.81/0.98  --inst_learning_factor                  2
% 1.81/0.98  --inst_start_prop_sim_after_learn       3
% 1.81/0.98  --inst_sel_renew                        solver
% 1.81/0.98  --inst_lit_activity_flag                true
% 1.81/0.98  --inst_restr_to_given                   false
% 1.81/0.98  --inst_activity_threshold               500
% 1.81/0.98  --inst_out_proof                        true
% 1.81/0.98  
% 1.81/0.98  ------ Resolution Options
% 1.81/0.98  
% 1.81/0.98  --resolution_flag                       true
% 1.81/0.98  --res_lit_sel                           adaptive
% 1.81/0.98  --res_lit_sel_side                      none
% 1.81/0.98  --res_ordering                          kbo
% 1.81/0.98  --res_to_prop_solver                    active
% 1.81/0.98  --res_prop_simpl_new                    false
% 1.81/0.98  --res_prop_simpl_given                  true
% 1.81/0.98  --res_passive_queue_type                priority_queues
% 1.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/0.98  --res_passive_queues_freq               [15;5]
% 1.81/0.98  --res_forward_subs                      full
% 1.81/0.98  --res_backward_subs                     full
% 1.81/0.98  --res_forward_subs_resolution           true
% 1.81/0.98  --res_backward_subs_resolution          true
% 1.81/0.98  --res_orphan_elimination                true
% 1.81/0.98  --res_time_limit                        2.
% 1.81/0.98  --res_out_proof                         true
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Options
% 1.81/0.98  
% 1.81/0.98  --superposition_flag                    true
% 1.81/0.98  --sup_passive_queue_type                priority_queues
% 1.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.81/0.98  --demod_completeness_check              fast
% 1.81/0.98  --demod_use_ground                      true
% 1.81/0.98  --sup_to_prop_solver                    passive
% 1.81/0.98  --sup_prop_simpl_new                    true
% 1.81/0.98  --sup_prop_simpl_given                  true
% 1.81/0.98  --sup_fun_splitting                     false
% 1.81/0.98  --sup_smt_interval                      50000
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Simplification Setup
% 1.81/0.98  
% 1.81/0.98  --sup_indices_passive                   []
% 1.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_full_bw                           [BwDemod]
% 1.81/0.98  --sup_immed_triv                        [TrivRules]
% 1.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_immed_bw_main                     []
% 1.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  
% 1.81/0.98  ------ Combination Options
% 1.81/0.98  
% 1.81/0.98  --comb_res_mult                         3
% 1.81/0.98  --comb_sup_mult                         2
% 1.81/0.98  --comb_inst_mult                        10
% 1.81/0.98  
% 1.81/0.98  ------ Debug Options
% 1.81/0.98  
% 1.81/0.98  --dbg_backtrace                         false
% 1.81/0.98  --dbg_dump_prop_clauses                 false
% 1.81/0.98  --dbg_dump_prop_clauses_file            -
% 1.81/0.98  --dbg_out_stat                          false
% 1.81/0.98  ------ Parsing...
% 1.81/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.81/0.98  ------ Proving...
% 1.81/0.98  ------ Problem Properties 
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  clauses                                 18
% 1.81/0.98  conjectures                             6
% 1.81/0.98  EPR                                     5
% 1.81/0.98  Horn                                    12
% 1.81/0.98  unary                                   1
% 1.81/0.98  binary                                  7
% 1.81/0.98  lits                                    50
% 1.81/0.98  lits eq                                 22
% 1.81/0.98  fd_pure                                 0
% 1.81/0.98  fd_pseudo                               0
% 1.81/0.98  fd_cond                                 0
% 1.81/0.98  fd_pseudo_cond                          2
% 1.81/0.98  AC symbols                              0
% 1.81/0.98  
% 1.81/0.98  ------ Schedule dynamic 5 is on 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  ------ 
% 1.81/0.98  Current options:
% 1.81/0.98  ------ 
% 1.81/0.98  
% 1.81/0.98  ------ Input Options
% 1.81/0.98  
% 1.81/0.98  --out_options                           all
% 1.81/0.98  --tptp_safe_out                         true
% 1.81/0.98  --problem_path                          ""
% 1.81/0.98  --include_path                          ""
% 1.81/0.98  --clausifier                            res/vclausify_rel
% 1.81/0.98  --clausifier_options                    --mode clausify
% 1.81/0.98  --stdin                                 false
% 1.81/0.98  --stats_out                             all
% 1.81/0.98  
% 1.81/0.98  ------ General Options
% 1.81/0.98  
% 1.81/0.98  --fof                                   false
% 1.81/0.98  --time_out_real                         305.
% 1.81/0.98  --time_out_virtual                      -1.
% 1.81/0.98  --symbol_type_check                     false
% 1.81/0.98  --clausify_out                          false
% 1.81/0.98  --sig_cnt_out                           false
% 1.81/0.98  --trig_cnt_out                          false
% 1.81/0.98  --trig_cnt_out_tolerance                1.
% 1.81/0.98  --trig_cnt_out_sk_spl                   false
% 1.81/0.98  --abstr_cl_out                          false
% 1.81/0.98  
% 1.81/0.98  ------ Global Options
% 1.81/0.98  
% 1.81/0.98  --schedule                              default
% 1.81/0.98  --add_important_lit                     false
% 1.81/0.98  --prop_solver_per_cl                    1000
% 1.81/0.98  --min_unsat_core                        false
% 1.81/0.98  --soft_assumptions                      false
% 1.81/0.98  --soft_lemma_size                       3
% 1.81/0.98  --prop_impl_unit_size                   0
% 1.81/0.98  --prop_impl_unit                        []
% 1.81/0.98  --share_sel_clauses                     true
% 1.81/0.98  --reset_solvers                         false
% 1.81/0.98  --bc_imp_inh                            [conj_cone]
% 1.81/0.98  --conj_cone_tolerance                   3.
% 1.81/0.98  --extra_neg_conj                        none
% 1.81/0.98  --large_theory_mode                     true
% 1.81/0.98  --prolific_symb_bound                   200
% 1.81/0.98  --lt_threshold                          2000
% 1.81/0.98  --clause_weak_htbl                      true
% 1.81/0.98  --gc_record_bc_elim                     false
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing Options
% 1.81/0.98  
% 1.81/0.98  --preprocessing_flag                    true
% 1.81/0.98  --time_out_prep_mult                    0.1
% 1.81/0.98  --splitting_mode                        input
% 1.81/0.98  --splitting_grd                         true
% 1.81/0.98  --splitting_cvd                         false
% 1.81/0.98  --splitting_cvd_svl                     false
% 1.81/0.98  --splitting_nvd                         32
% 1.81/0.98  --sub_typing                            true
% 1.81/0.98  --prep_gs_sim                           true
% 1.81/0.98  --prep_unflatten                        true
% 1.81/0.98  --prep_res_sim                          true
% 1.81/0.98  --prep_upred                            true
% 1.81/0.98  --prep_sem_filter                       exhaustive
% 1.81/0.98  --prep_sem_filter_out                   false
% 1.81/0.98  --pred_elim                             true
% 1.81/0.98  --res_sim_input                         true
% 1.81/0.98  --eq_ax_congr_red                       true
% 1.81/0.98  --pure_diseq_elim                       true
% 1.81/0.98  --brand_transform                       false
% 1.81/0.98  --non_eq_to_eq                          false
% 1.81/0.98  --prep_def_merge                        true
% 1.81/0.98  --prep_def_merge_prop_impl              false
% 1.81/0.98  --prep_def_merge_mbd                    true
% 1.81/0.98  --prep_def_merge_tr_red                 false
% 1.81/0.98  --prep_def_merge_tr_cl                  false
% 1.81/0.98  --smt_preprocessing                     true
% 1.81/0.98  --smt_ac_axioms                         fast
% 1.81/0.98  --preprocessed_out                      false
% 1.81/0.98  --preprocessed_stats                    false
% 1.81/0.98  
% 1.81/0.98  ------ Abstraction refinement Options
% 1.81/0.98  
% 1.81/0.98  --abstr_ref                             []
% 1.81/0.98  --abstr_ref_prep                        false
% 1.81/0.98  --abstr_ref_until_sat                   false
% 1.81/0.98  --abstr_ref_sig_restrict                funpre
% 1.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/0.98  --abstr_ref_under                       []
% 1.81/0.98  
% 1.81/0.98  ------ SAT Options
% 1.81/0.98  
% 1.81/0.98  --sat_mode                              false
% 1.81/0.98  --sat_fm_restart_options                ""
% 1.81/0.98  --sat_gr_def                            false
% 1.81/0.98  --sat_epr_types                         true
% 1.81/0.98  --sat_non_cyclic_types                  false
% 1.81/0.98  --sat_finite_models                     false
% 1.81/0.98  --sat_fm_lemmas                         false
% 1.81/0.98  --sat_fm_prep                           false
% 1.81/0.98  --sat_fm_uc_incr                        true
% 1.81/0.98  --sat_out_model                         small
% 1.81/0.98  --sat_out_clauses                       false
% 1.81/0.98  
% 1.81/0.98  ------ QBF Options
% 1.81/0.98  
% 1.81/0.98  --qbf_mode                              false
% 1.81/0.98  --qbf_elim_univ                         false
% 1.81/0.98  --qbf_dom_inst                          none
% 1.81/0.98  --qbf_dom_pre_inst                      false
% 1.81/0.98  --qbf_sk_in                             false
% 1.81/0.98  --qbf_pred_elim                         true
% 1.81/0.98  --qbf_split                             512
% 1.81/0.98  
% 1.81/0.98  ------ BMC1 Options
% 1.81/0.98  
% 1.81/0.98  --bmc1_incremental                      false
% 1.81/0.98  --bmc1_axioms                           reachable_all
% 1.81/0.98  --bmc1_min_bound                        0
% 1.81/0.98  --bmc1_max_bound                        -1
% 1.81/0.98  --bmc1_max_bound_default                -1
% 1.81/0.98  --bmc1_symbol_reachability              true
% 1.81/0.98  --bmc1_property_lemmas                  false
% 1.81/0.98  --bmc1_k_induction                      false
% 1.81/0.98  --bmc1_non_equiv_states                 false
% 1.81/0.98  --bmc1_deadlock                         false
% 1.81/0.98  --bmc1_ucm                              false
% 1.81/0.98  --bmc1_add_unsat_core                   none
% 1.81/0.98  --bmc1_unsat_core_children              false
% 1.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/0.98  --bmc1_out_stat                         full
% 1.81/0.98  --bmc1_ground_init                      false
% 1.81/0.98  --bmc1_pre_inst_next_state              false
% 1.81/0.98  --bmc1_pre_inst_state                   false
% 1.81/0.98  --bmc1_pre_inst_reach_state             false
% 1.81/0.98  --bmc1_out_unsat_core                   false
% 1.81/0.98  --bmc1_aig_witness_out                  false
% 1.81/0.98  --bmc1_verbose                          false
% 1.81/0.98  --bmc1_dump_clauses_tptp                false
% 1.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.81/0.98  --bmc1_dump_file                        -
% 1.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.81/0.98  --bmc1_ucm_extend_mode                  1
% 1.81/0.98  --bmc1_ucm_init_mode                    2
% 1.81/0.98  --bmc1_ucm_cone_mode                    none
% 1.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.81/0.98  --bmc1_ucm_relax_model                  4
% 1.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/0.98  --bmc1_ucm_layered_model                none
% 1.81/0.98  --bmc1_ucm_max_lemma_size               10
% 1.81/0.98  
% 1.81/0.98  ------ AIG Options
% 1.81/0.98  
% 1.81/0.98  --aig_mode                              false
% 1.81/0.98  
% 1.81/0.98  ------ Instantiation Options
% 1.81/0.98  
% 1.81/0.98  --instantiation_flag                    true
% 1.81/0.98  --inst_sos_flag                         false
% 1.81/0.98  --inst_sos_phase                        true
% 1.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/0.98  --inst_lit_sel_side                     none
% 1.81/0.98  --inst_solver_per_active                1400
% 1.81/0.98  --inst_solver_calls_frac                1.
% 1.81/0.98  --inst_passive_queue_type               priority_queues
% 1.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/0.98  --inst_passive_queues_freq              [25;2]
% 1.81/0.98  --inst_dismatching                      true
% 1.81/0.98  --inst_eager_unprocessed_to_passive     true
% 1.81/0.98  --inst_prop_sim_given                   true
% 1.81/0.98  --inst_prop_sim_new                     false
% 1.81/0.98  --inst_subs_new                         false
% 1.81/0.98  --inst_eq_res_simp                      false
% 1.81/0.98  --inst_subs_given                       false
% 1.81/0.98  --inst_orphan_elimination               true
% 1.81/0.98  --inst_learning_loop_flag               true
% 1.81/0.98  --inst_learning_start                   3000
% 1.81/0.98  --inst_learning_factor                  2
% 1.81/0.98  --inst_start_prop_sim_after_learn       3
% 1.81/0.98  --inst_sel_renew                        solver
% 1.81/0.98  --inst_lit_activity_flag                true
% 1.81/0.98  --inst_restr_to_given                   false
% 1.81/0.98  --inst_activity_threshold               500
% 1.81/0.98  --inst_out_proof                        true
% 1.81/0.98  
% 1.81/0.98  ------ Resolution Options
% 1.81/0.98  
% 1.81/0.98  --resolution_flag                       false
% 1.81/0.98  --res_lit_sel                           adaptive
% 1.81/0.98  --res_lit_sel_side                      none
% 1.81/0.98  --res_ordering                          kbo
% 1.81/0.98  --res_to_prop_solver                    active
% 1.81/0.98  --res_prop_simpl_new                    false
% 1.81/0.98  --res_prop_simpl_given                  true
% 1.81/0.98  --res_passive_queue_type                priority_queues
% 1.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/0.98  --res_passive_queues_freq               [15;5]
% 1.81/0.98  --res_forward_subs                      full
% 1.81/0.98  --res_backward_subs                     full
% 1.81/0.98  --res_forward_subs_resolution           true
% 1.81/0.98  --res_backward_subs_resolution          true
% 1.81/0.98  --res_orphan_elimination                true
% 1.81/0.98  --res_time_limit                        2.
% 1.81/0.98  --res_out_proof                         true
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Options
% 1.81/0.98  
% 1.81/0.98  --superposition_flag                    true
% 1.81/0.98  --sup_passive_queue_type                priority_queues
% 1.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.81/0.98  --demod_completeness_check              fast
% 1.81/0.98  --demod_use_ground                      true
% 1.81/0.98  --sup_to_prop_solver                    passive
% 1.81/0.98  --sup_prop_simpl_new                    true
% 1.81/0.98  --sup_prop_simpl_given                  true
% 1.81/0.98  --sup_fun_splitting                     false
% 1.81/0.98  --sup_smt_interval                      50000
% 1.81/0.98  
% 1.81/0.98  ------ Superposition Simplification Setup
% 1.81/0.98  
% 1.81/0.98  --sup_indices_passive                   []
% 1.81/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_full_bw                           [BwDemod]
% 1.81/0.98  --sup_immed_triv                        [TrivRules]
% 1.81/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_immed_bw_main                     []
% 1.81/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/0.98  
% 1.81/0.98  ------ Combination Options
% 1.81/0.98  
% 1.81/0.98  --comb_res_mult                         3
% 1.81/0.98  --comb_sup_mult                         2
% 1.81/0.98  --comb_inst_mult                        10
% 1.81/0.98  
% 1.81/0.98  ------ Debug Options
% 1.81/0.98  
% 1.81/0.98  --dbg_backtrace                         false
% 1.81/0.98  --dbg_dump_prop_clauses                 false
% 1.81/0.98  --dbg_dump_prop_clauses_file            -
% 1.81/0.98  --dbg_out_stat                          false
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  ------ Proving...
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  % SZS status Theorem for theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  fof(f3,axiom,(
% 1.81/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f9,plain,(
% 1.81/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/0.98    inference(ennf_transformation,[],[f3])).
% 1.81/0.98  
% 1.81/0.98  fof(f10,plain,(
% 1.81/0.98    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.98    inference(flattening,[],[f9])).
% 1.81/0.98  
% 1.81/0.98  fof(f16,plain,(
% 1.81/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.98    inference(nnf_transformation,[],[f10])).
% 1.81/0.98  
% 1.81/0.98  fof(f17,plain,(
% 1.81/0.98    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.98    inference(rectify,[],[f16])).
% 1.81/0.98  
% 1.81/0.98  fof(f18,plain,(
% 1.81/0.98    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f19,plain,(
% 1.81/0.98    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 1.81/0.98  
% 1.81/0.98  fof(f32,plain,(
% 1.81/0.98    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f19])).
% 1.81/0.98  
% 1.81/0.98  fof(f6,conjecture,(
% 1.81/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 1.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f7,negated_conjecture,(
% 1.81/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 1.81/0.98    inference(negated_conjecture,[],[f6])).
% 1.81/0.98  
% 1.81/0.98  fof(f14,plain,(
% 1.81/0.98    ? [X0,X1,X2] : (((v2_funct_1(X2) <~> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.81/0.98    inference(ennf_transformation,[],[f7])).
% 1.81/0.98  
% 1.81/0.98  fof(f15,plain,(
% 1.81/0.98    ? [X0,X1,X2] : ((v2_funct_1(X2) <~> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.81/0.98    inference(flattening,[],[f14])).
% 1.81/0.98  
% 1.81/0.98  fof(f21,plain,(
% 1.81/0.98    ? [X0,X1,X2] : (((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | v2_funct_1(X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.81/0.98    inference(nnf_transformation,[],[f15])).
% 1.81/0.98  
% 1.81/0.98  fof(f22,plain,(
% 1.81/0.98    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.81/0.98    inference(flattening,[],[f21])).
% 1.81/0.98  
% 1.81/0.98  fof(f23,plain,(
% 1.81/0.98    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.81/0.98    inference(rectify,[],[f22])).
% 1.81/0.98  
% 1.81/0.98  fof(f25,plain,(
% 1.81/0.98    ( ! [X2,X0] : (? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => (sK5 != sK6 & k1_funct_1(X2,sK5) = k1_funct_1(X2,sK6) & r2_hidden(sK6,X0) & r2_hidden(sK5,X0))) )),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f24,plain,(
% 1.81/0.98    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((? [X4,X3] : (X3 != X4 & k1_funct_1(sK4,X3) = k1_funct_1(sK4,X4) & r2_hidden(X4,sK2) & r2_hidden(X3,sK2)) | ~v2_funct_1(sK4)) & (! [X6,X5] : (X5 = X6 | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK2)) | v2_funct_1(sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 1.81/0.98    introduced(choice_axiom,[])).
% 1.81/0.98  
% 1.81/0.98  fof(f26,plain,(
% 1.81/0.98    ((sK5 != sK6 & k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) & r2_hidden(sK6,sK2) & r2_hidden(sK5,sK2)) | ~v2_funct_1(sK4)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK2)) | v2_funct_1(sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 1.81/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f23,f25,f24])).
% 1.81/0.98  
% 1.81/0.98  fof(f41,plain,(
% 1.81/0.98    v1_funct_1(sK4)),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f1,axiom,(
% 1.81/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f8,plain,(
% 1.81/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.81/0.98    inference(ennf_transformation,[],[f1])).
% 1.81/0.98  
% 1.81/0.98  fof(f27,plain,(
% 1.81/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f8])).
% 1.81/0.98  
% 1.81/0.98  fof(f43,plain,(
% 1.81/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f2,axiom,(
% 1.81/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f28,plain,(
% 1.81/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.81/0.98    inference(cnf_transformation,[],[f2])).
% 1.81/0.98  
% 1.81/0.98  fof(f42,plain,(
% 1.81/0.98    v1_funct_2(sK4,sK2,sK3)),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f5,axiom,(
% 1.81/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f12,plain,(
% 1.81/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.98    inference(ennf_transformation,[],[f5])).
% 1.81/0.98  
% 1.81/0.98  fof(f13,plain,(
% 1.81/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.98    inference(flattening,[],[f12])).
% 1.81/0.98  
% 1.81/0.98  fof(f20,plain,(
% 1.81/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.98    inference(nnf_transformation,[],[f13])).
% 1.81/0.98  
% 1.81/0.98  fof(f35,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.98    inference(cnf_transformation,[],[f20])).
% 1.81/0.98  
% 1.81/0.98  fof(f4,axiom,(
% 1.81/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.81/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.81/0.98  
% 1.81/0.98  fof(f11,plain,(
% 1.81/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.98    inference(ennf_transformation,[],[f4])).
% 1.81/0.98  
% 1.81/0.98  fof(f34,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.98    inference(cnf_transformation,[],[f11])).
% 1.81/0.98  
% 1.81/0.98  fof(f31,plain,(
% 1.81/0.98    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f19])).
% 1.81/0.98  
% 1.81/0.98  fof(f46,plain,(
% 1.81/0.98    r2_hidden(sK5,sK2) | ~v2_funct_1(sK4)),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f47,plain,(
% 1.81/0.98    r2_hidden(sK6,sK2) | ~v2_funct_1(sK4)),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f30,plain,(
% 1.81/0.98    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f19])).
% 1.81/0.98  
% 1.81/0.98  fof(f49,plain,(
% 1.81/0.98    sK5 != sK6 | ~v2_funct_1(sK4)),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f48,plain,(
% 1.81/0.98    k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) | ~v2_funct_1(sK4)),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f29,plain,(
% 1.81/0.98    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f19])).
% 1.81/0.98  
% 1.81/0.98  fof(f33,plain,(
% 1.81/0.98    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f19])).
% 1.81/0.98  
% 1.81/0.98  fof(f45,plain,(
% 1.81/0.98    ( ! [X6,X5] : (X5 = X6 | k1_funct_1(sK4,X5) != k1_funct_1(sK4,X6) | ~r2_hidden(X6,sK2) | ~r2_hidden(X5,sK2) | v2_funct_1(sK4)) )),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f44,plain,(
% 1.81/0.98    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 1.81/0.98    inference(cnf_transformation,[],[f26])).
% 1.81/0.98  
% 1.81/0.98  fof(f36,plain,(
% 1.81/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.98    inference(cnf_transformation,[],[f20])).
% 1.81/0.98  
% 1.81/0.98  fof(f54,plain,(
% 1.81/0.98    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.81/0.98    inference(equality_resolution,[],[f36])).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3,plain,
% 1.81/0.98      ( ~ v1_funct_1(X0)
% 1.81/0.98      | v2_funct_1(X0)
% 1.81/0.98      | ~ v1_relat_1(X0)
% 1.81/0.98      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 1.81/0.98      inference(cnf_transformation,[],[f32]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_22,negated_conjecture,
% 1.81/0.98      ( v1_funct_1(sK4) ),
% 1.81/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_454,plain,
% 1.81/0.98      ( v2_funct_1(X0)
% 1.81/0.98      | ~ v1_relat_1(X0)
% 1.81/0.98      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
% 1.81/0.98      | sK4 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_22]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_455,plain,
% 1.81/0.98      ( v2_funct_1(sK4)
% 1.81/0.98      | ~ v1_relat_1(sK4)
% 1.81/0.98      | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_454]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1635,plain,
% 1.81/0.98      ( v2_funct_1(sK4)
% 1.81/0.98      | ~ v1_relat_1(sK4)
% 1.81/0.98      | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_455]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1927,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1698,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1652,plain,( X0_48 = X0_48 ),theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2068,plain,
% 1.81/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1652]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_0,plain,
% 1.81/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.81/0.98      | ~ v1_relat_1(X1)
% 1.81/0.98      | v1_relat_1(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f27]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_20,negated_conjecture,
% 1.81/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 1.81/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_245,plain,
% 1.81/0.98      ( ~ v1_relat_1(X0)
% 1.81/0.98      | v1_relat_1(X1)
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0)
% 1.81/0.98      | sK4 != X1 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_246,plain,
% 1.81/0.98      ( ~ v1_relat_1(X0)
% 1.81/0.98      | v1_relat_1(sK4)
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_245]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1640,plain,
% 1.81/0.98      ( ~ v1_relat_1(X0_47)
% 1.81/0.98      | v1_relat_1(sK4)
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(X0_47) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_246]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2063,plain,
% 1.81/0.98      ( ~ v1_relat_1(k2_zfmisc_1(X0_47,X1_47))
% 1.81/0.98      | v1_relat_1(sK4)
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1640]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2109,plain,
% 1.81/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | v1_relat_1(sK4)
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2063]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2110,plain,
% 1.81/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 1.81/0.98      | v1_relat_1(sK4) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2109]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1,plain,
% 1.81/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.81/0.98      inference(cnf_transformation,[],[f28]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1647,plain,
% 1.81/0.98      ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2132,plain,
% 1.81/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1647]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2133,plain,
% 1.81/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2132]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2399,plain,
% 1.81/0.98      ( v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4)) ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_1927,c_1698,c_2068,c_2110,c_2133]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2400,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK0(sK4)) = k1_funct_1(sK4,sK1(sK4))
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_2399]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_21,negated_conjecture,
% 1.81/0.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 1.81/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_13,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/0.98      | k1_relset_1(X1,X2,X0) = X1
% 1.81/0.98      | k1_xboole_0 = X2 ),
% 1.81/0.98      inference(cnf_transformation,[],[f35]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_260,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/0.98      | k1_relset_1(X1,X2,X0) = X1
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | sK4 != X0
% 1.81/0.98      | k1_xboole_0 = X2 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_261,plain,
% 1.81/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 1.81/0.98      | k1_relset_1(X0,X1,sK4) = X0
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | k1_xboole_0 = X1 ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_260]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_511,plain,
% 1.81/0.98      ( k1_relset_1(X0,X1,sK4) = X0
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | sK3 != X1
% 1.81/0.98      | sK2 != X0
% 1.81/0.98      | sK4 != sK4
% 1.81/0.98      | k1_xboole_0 = X1 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_261]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_512,plain,
% 1.81/0.98      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | k1_xboole_0 = sK3 ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_511]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1074,plain,
% 1.81/0.98      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 1.81/0.98      inference(equality_resolution_simp,[status(thm)],[c_512]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1631,plain,
% 1.81/0.98      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_1074]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_7,plain,
% 1.81/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f34]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_296,plain,
% 1.81/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | sK4 != X2 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_297,plain,
% 1.81/0.98      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_296]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1639,plain,
% 1.81/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | k1_relset_1(X0_47,X1_47,sK4) = k1_relat_1(sK4) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_297]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2091,plain,
% 1.81/0.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 1.81/0.98      inference(equality_resolution,[status(thm)],[c_1639]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2195,plain,
% 1.81/0.98      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_1631,c_2091]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_4,plain,
% 1.81/0.98      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | v2_funct_1(X0)
% 1.81/0.98      | ~ v1_relat_1(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_441,plain,
% 1.81/0.98      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 1.81/0.98      | v2_funct_1(X0)
% 1.81/0.98      | ~ v1_relat_1(X0)
% 1.81/0.98      | sK4 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_442,plain,
% 1.81/0.98      ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 1.81/0.98      | v2_funct_1(sK4)
% 1.81/0.98      | ~ v1_relat_1(sK4) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_441]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1636,plain,
% 1.81/0.98      ( r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 1.81/0.98      | v2_funct_1(sK4)
% 1.81/0.98      | ~ v1_relat_1(sK4) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_442]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1926,plain,
% 1.81/0.98      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_443,plain,
% 1.81/0.98      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2355,plain,
% 1.81/0.98      ( v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_1926,c_443,c_2068,c_2110,c_2133]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2356,plain,
% 1.81/0.98      ( r2_hidden(sK1(sK4),k1_relat_1(sK4)) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_2355]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2524,plain,
% 1.81/0.98      ( sK3 = k1_xboole_0
% 1.81/0.98      | r2_hidden(sK1(sK4),sK2) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2195,c_2356]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_17,negated_conjecture,
% 1.81/0.98      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 1.81/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_29,plain,
% 1.81/0.98      ( r2_hidden(sK5,sK2) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_16,negated_conjecture,
% 1.81/0.98      ( r2_hidden(sK6,sK2) | ~ v2_funct_1(sK4) ),
% 1.81/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_30,plain,
% 1.81/0.98      ( r2_hidden(sK6,sK2) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_5,plain,
% 1.81/0.98      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.81/0.98      | ~ v1_funct_1(X0)
% 1.81/0.98      | v2_funct_1(X0)
% 1.81/0.98      | ~ v1_relat_1(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f30]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_428,plain,
% 1.81/0.98      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 1.81/0.98      | v2_funct_1(X0)
% 1.81/0.98      | ~ v1_relat_1(X0)
% 1.81/0.98      | sK4 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_429,plain,
% 1.81/0.98      ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
% 1.81/0.98      | v2_funct_1(sK4)
% 1.81/0.98      | ~ v1_relat_1(sK4) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_428]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_430,plain,
% 1.81/0.98      ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1653,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1682,plain,
% 1.81/0.98      ( sK5 = sK5 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1653]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_14,negated_conjecture,
% 1.81/0.98      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 1.81/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1646,negated_conjecture,
% 1.81/0.98      ( ~ v2_funct_1(sK4) | sK5 != sK6 ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1685,plain,
% 1.81/0.98      ( sK5 != sK6 | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_15,negated_conjecture,
% 1.81/0.98      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 1.81/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1645,negated_conjecture,
% 1.81/0.98      ( ~ v2_funct_1(sK4) | k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1686,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_6,plain,
% 1.81/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.81/0.98      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.81/0.98      | ~ v1_funct_1(X1)
% 1.81/0.98      | ~ v2_funct_1(X1)
% 1.81/0.98      | ~ v1_relat_1(X1)
% 1.81/0.98      | X0 = X2
% 1.81/0.98      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 1.81/0.98      inference(cnf_transformation,[],[f29]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_404,plain,
% 1.81/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.81/0.98      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.81/0.98      | ~ v2_funct_1(X1)
% 1.81/0.98      | ~ v1_relat_1(X1)
% 1.81/0.98      | X0 = X2
% 1.81/0.98      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 1.81/0.98      | sK4 != X1 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_405,plain,
% 1.81/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 1.81/0.98      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 1.81/0.98      | ~ v2_funct_1(sK4)
% 1.81/0.98      | ~ v1_relat_1(sK4)
% 1.81/0.98      | X1 = X0
% 1.81/0.98      | k1_funct_1(sK4,X0) != k1_funct_1(sK4,X1) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_404]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1638,plain,
% 1.81/0.98      ( ~ r2_hidden(X0_49,k1_relat_1(sK4))
% 1.81/0.98      | ~ r2_hidden(X1_49,k1_relat_1(sK4))
% 1.81/0.98      | ~ v2_funct_1(sK4)
% 1.81/0.98      | ~ v1_relat_1(sK4)
% 1.81/0.98      | k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
% 1.81/0.98      | X1_49 = X0_49 ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_405]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1649,plain,
% 1.81/0.98      ( ~ v2_funct_1(sK4) | ~ v1_relat_1(sK4) | sP0_iProver_split ),
% 1.81/0.98      inference(splitting,
% 1.81/0.98                [splitting(split),new_symbols(definition,[])],
% 1.81/0.98                [c_1638]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1694,plain,
% 1.81/0.98      ( v2_funct_1(sK4) != iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top
% 1.81/0.98      | sP0_iProver_split = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1649]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2,plain,
% 1.81/0.98      ( ~ v1_funct_1(X0)
% 1.81/0.98      | v2_funct_1(X0)
% 1.81/0.98      | ~ v1_relat_1(X0)
% 1.81/0.98      | sK1(X0) != sK0(X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_467,plain,
% 1.81/0.98      ( v2_funct_1(X0)
% 1.81/0.98      | ~ v1_relat_1(X0)
% 1.81/0.98      | sK1(X0) != sK0(X0)
% 1.81/0.98      | sK4 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_22]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_468,plain,
% 1.81/0.98      ( v2_funct_1(sK4) | ~ v1_relat_1(sK4) | sK1(sK4) != sK0(sK4) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_467]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1634,plain,
% 1.81/0.98      ( v2_funct_1(sK4) | ~ v1_relat_1(sK4) | sK1(sK4) != sK0(sK4) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_468]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1699,plain,
% 1.81/0.98      ( sK1(sK4) != sK0(sK4)
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1657,plain,
% 1.81/0.98      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 1.81/0.98      theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2254,plain,
% 1.81/0.98      ( sK6 != X0_49 | sK5 != X0_49 | sK5 = sK6 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1657]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2255,plain,
% 1.81/0.98      ( sK6 != sK5 | sK5 = sK6 | sK5 != sK5 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2254]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1648,plain,
% 1.81/0.98      ( ~ r2_hidden(X0_49,k1_relat_1(sK4))
% 1.81/0.98      | ~ r2_hidden(X1_49,k1_relat_1(sK4))
% 1.81/0.98      | k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
% 1.81/0.98      | X1_49 = X0_49
% 1.81/0.98      | ~ sP0_iProver_split ),
% 1.81/0.98      inference(splitting,
% 1.81/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.81/0.98                [c_1638]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2366,plain,
% 1.81/0.98      ( ~ r2_hidden(X0_49,k1_relat_1(sK4))
% 1.81/0.98      | ~ r2_hidden(sK6,k1_relat_1(sK4))
% 1.81/0.98      | ~ sP0_iProver_split
% 1.81/0.98      | k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,sK6)
% 1.81/0.98      | sK6 = X0_49 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1648]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2372,plain,
% 1.81/0.98      ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,sK6)
% 1.81/0.98      | sK6 = X0_49
% 1.81/0.98      | r2_hidden(X0_49,k1_relat_1(sK4)) != iProver_top
% 1.81/0.98      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 1.81/0.98      | sP0_iProver_split != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2374,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK5) != k1_funct_1(sK4,sK6)
% 1.81/0.98      | sK6 = sK5
% 1.81/0.98      | r2_hidden(sK6,k1_relat_1(sK4)) != iProver_top
% 1.81/0.98      | r2_hidden(sK5,k1_relat_1(sK4)) != iProver_top
% 1.81/0.98      | sP0_iProver_split != iProver_top ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2372]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1667,plain,
% 1.81/0.98      ( ~ r2_hidden(X0_49,X0_47)
% 1.81/0.98      | r2_hidden(X1_49,X1_47)
% 1.81/0.98      | X1_49 != X0_49
% 1.81/0.98      | X1_47 != X0_47 ),
% 1.81/0.98      theory(equality) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2227,plain,
% 1.81/0.98      ( r2_hidden(X0_49,X0_47)
% 1.81/0.98      | ~ r2_hidden(sK5,sK2)
% 1.81/0.98      | X0_49 != sK5
% 1.81/0.98      | X0_47 != sK2 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1667]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2378,plain,
% 1.81/0.98      ( r2_hidden(sK5,k1_relat_1(sK4))
% 1.81/0.98      | ~ r2_hidden(sK5,sK2)
% 1.81/0.98      | sK5 != sK5
% 1.81/0.98      | k1_relat_1(sK4) != sK2 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2227]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2379,plain,
% 1.81/0.98      ( sK5 != sK5
% 1.81/0.98      | k1_relat_1(sK4) != sK2
% 1.81/0.98      | r2_hidden(sK5,k1_relat_1(sK4)) = iProver_top
% 1.81/0.98      | r2_hidden(sK5,sK2) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2378]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1923,plain,
% 1.81/0.98      ( v2_funct_1(sK4) != iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top
% 1.81/0.98      | sP0_iProver_split = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1649]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2238,plain,
% 1.81/0.98      ( v2_funct_1(sK4) != iProver_top
% 1.81/0.98      | sP0_iProver_split = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_1923,c_1694,c_2068,c_2110,c_2133]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2405,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
% 1.81/0.98      | sP0_iProver_split = iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2400,c_2238]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1637,plain,
% 1.81/0.98      ( r2_hidden(sK0(sK4),k1_relat_1(sK4))
% 1.81/0.98      | v2_funct_1(sK4)
% 1.81/0.98      | ~ v1_relat_1(sK4) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_429]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1925,plain,
% 1.81/0.98      ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1637]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2348,plain,
% 1.81/0.98      ( v2_funct_1(sK4) = iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_1925,c_430,c_2068,c_2110,c_2133]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2349,plain,
% 1.81/0.98      ( r2_hidden(sK0(sK4),k1_relat_1(sK4)) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_2348]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2525,plain,
% 1.81/0.98      ( sK3 = k1_xboole_0
% 1.81/0.98      | r2_hidden(sK0(sK4),sK2) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2195,c_2349]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2232,plain,
% 1.81/0.98      ( r2_hidden(X0_49,X0_47)
% 1.81/0.98      | ~ r2_hidden(sK6,sK2)
% 1.81/0.98      | X0_49 != sK6
% 1.81/0.98      | X0_47 != sK2 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1667]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2593,plain,
% 1.81/0.98      ( r2_hidden(sK6,k1_relat_1(sK4))
% 1.81/0.98      | ~ r2_hidden(sK6,sK2)
% 1.81/0.98      | sK6 != sK6
% 1.81/0.98      | k1_relat_1(sK4) != sK2 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_2232]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2597,plain,
% 1.81/0.98      ( sK6 != sK6
% 1.81/0.98      | k1_relat_1(sK4) != sK2
% 1.81/0.98      | r2_hidden(sK6,k1_relat_1(sK4)) = iProver_top
% 1.81/0.98      | r2_hidden(sK6,sK2) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2593]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2639,plain,
% 1.81/0.98      ( sK6 = sK6 ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1653]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_18,negated_conjecture,
% 1.81/0.98      ( ~ r2_hidden(X0,sK2)
% 1.81/0.98      | ~ r2_hidden(X1,sK2)
% 1.81/0.98      | v2_funct_1(sK4)
% 1.81/0.98      | X1 = X0
% 1.81/0.98      | k1_funct_1(sK4,X1) != k1_funct_1(sK4,X0) ),
% 1.81/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1642,negated_conjecture,
% 1.81/0.98      ( ~ r2_hidden(X0_49,sK2)
% 1.81/0.98      | ~ r2_hidden(X1_49,sK2)
% 1.81/0.98      | v2_funct_1(sK4)
% 1.81/0.98      | k1_funct_1(sK4,X1_49) != k1_funct_1(sK4,X0_49)
% 1.81/0.98      | X1_49 = X0_49 ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2803,plain,
% 1.81/0.98      ( ~ r2_hidden(sK1(sK4),sK2)
% 1.81/0.98      | ~ r2_hidden(sK0(sK4),sK2)
% 1.81/0.98      | v2_funct_1(sK4)
% 1.81/0.98      | k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
% 1.81/0.98      | sK1(sK4) = sK0(sK4) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1642]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2804,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK1(sK4)) != k1_funct_1(sK4,sK0(sK4))
% 1.81/0.98      | sK1(sK4) = sK0(sK4)
% 1.81/0.98      | r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK4),sK2) != iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2803]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2802,plain,
% 1.81/0.98      ( ~ r2_hidden(sK1(sK4),k1_relat_1(sK4))
% 1.81/0.98      | ~ r2_hidden(sK0(sK4),k1_relat_1(sK4))
% 1.81/0.98      | ~ sP0_iProver_split
% 1.81/0.98      | k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,sK1(sK4))
% 1.81/0.98      | sK1(sK4) = sK0(sK4) ),
% 1.81/0.98      inference(instantiation,[status(thm)],[c_1648]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2806,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,sK1(sK4))
% 1.81/0.98      | sK1(sK4) = sK0(sK4)
% 1.81/0.98      | r2_hidden(sK1(sK4),k1_relat_1(sK4)) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK4),k1_relat_1(sK4)) != iProver_top
% 1.81/0.98      | sP0_iProver_split != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_2802]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2811,plain,
% 1.81/0.98      ( sK3 = k1_xboole_0 | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_2524,c_29,c_30,c_430,c_443,c_1682,c_1685,c_1686,
% 1.81/0.98                 c_1694,c_1698,c_1699,c_2068,c_2110,c_2133,c_2195,c_2255,
% 1.81/0.98                 c_2374,c_2379,c_2405,c_2525,c_2597,c_2639,c_2804,c_2806]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2815,plain,
% 1.81/0.98      ( sK3 = k1_xboole_0 ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_2811,c_29,c_30,c_430,c_443,c_1682,c_1685,c_1686,
% 1.81/0.98                 c_1694,c_1698,c_1699,c_2068,c_2110,c_2133,c_2195,c_2255,
% 1.81/0.98                 c_2374,c_2379,c_2405,c_2524,c_2525,c_2597,c_2639,c_2804,
% 1.81/0.98                 c_2806]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_19,negated_conjecture,
% 1.81/0.98      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 1.81/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1641,negated_conjecture,
% 1.81/0.98      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2823,plain,
% 1.81/0.98      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2815,c_1641]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2824,plain,
% 1.81/0.98      ( sK2 = k1_xboole_0 ),
% 1.81/0.98      inference(equality_resolution_simp,[status(thm)],[c_2823]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1643,negated_conjecture,
% 1.81/0.98      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK4) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1920,plain,
% 1.81/0.98      ( r2_hidden(sK5,sK2) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1643]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2850,plain,
% 1.81/0.98      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2824,c_1920]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1918,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK5) = k1_funct_1(sK4,sK6)
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1645]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2406,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4))
% 1.81/0.98      | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2400,c_1918]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1921,plain,
% 1.81/0.98      ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
% 1.81/0.98      | X0_49 = X1_49
% 1.81/0.98      | r2_hidden(X0_49,sK2) != iProver_top
% 1.81/0.98      | r2_hidden(X1_49,sK2) != iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2421,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_49)
% 1.81/0.98      | k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.81/0.98      | sK1(sK4) = X0_49
% 1.81/0.98      | r2_hidden(X0_49,sK2) != iProver_top
% 1.81/0.98      | r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2406,c_1921]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2548,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.81/0.98      | sK1(sK4) = sK0(sK4)
% 1.81/0.98      | r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK4),sK2) != iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(equality_resolution,[status(thm)],[c_2421]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2608,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.81/0.98      | r2_hidden(sK1(sK4),sK2) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK4),sK2) != iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_2548,c_1699,c_2068,c_2110,c_2133]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2846,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.81/0.98      | r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top
% 1.81/0.98      | r2_hidden(sK0(sK4),k1_xboole_0) != iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2824,c_2608]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2818,plain,
% 1.81/0.98      ( k1_relset_1(sK2,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2815,c_2091]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_12,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.81/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.81/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.81/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_340,plain,
% 1.81/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.81/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | sK4 != X0 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_341,plain,
% 1.81/0.98      ( ~ v1_funct_2(sK4,k1_xboole_0,X0)
% 1.81/0.98      | k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_340]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_536,plain,
% 1.81/0.98      ( k1_relset_1(k1_xboole_0,X0,sK4) = k1_xboole_0
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | sK3 != X0
% 1.81/0.98      | sK2 != k1_xboole_0
% 1.81/0.98      | sK4 != sK4 ),
% 1.81/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_341]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_537,plain,
% 1.81/0.98      ( k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 1.81/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | sK2 != k1_xboole_0 ),
% 1.81/0.98      inference(unflattening,[status(thm)],[c_536]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1632,plain,
% 1.81/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 1.81/0.98      | k1_relset_1(k1_xboole_0,sK3,sK4) = k1_xboole_0
% 1.81/0.98      | sK2 != k1_xboole_0 ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_537]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2821,plain,
% 1.81/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.81/0.98      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 1.81/0.98      | sK2 != k1_xboole_0 ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2815,c_1632]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2832,plain,
% 1.81/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.81/0.98      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 1.81/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 1.81/0.98      inference(light_normalisation,[status(thm)],[c_2821,c_2824]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2833,plain,
% 1.81/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 1.81/0.98      inference(equality_resolution_simp,[status(thm)],[c_2832]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2837,plain,
% 1.81/0.98      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 1.81/0.98      inference(light_normalisation,[status(thm)],[c_2818,c_2824,c_2833]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3032,plain,
% 1.81/0.98      ( r2_hidden(sK1(sK4),k1_xboole_0) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2837,c_2356]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3033,plain,
% 1.81/0.98      ( r2_hidden(sK0(sK4),k1_xboole_0) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2837,c_2349]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3170,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5)
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_2846,c_3032,c_3033]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3177,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK6) = k1_funct_1(sK4,sK5) ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_3170,c_1918]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1924,plain,
% 1.81/0.98      ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
% 1.81/0.98      | X1_49 = X0_49
% 1.81/0.98      | r2_hidden(X1_49,k1_relat_1(sK4)) != iProver_top
% 1.81/0.98      | r2_hidden(X0_49,k1_relat_1(sK4)) != iProver_top
% 1.81/0.98      | sP0_iProver_split != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3034,plain,
% 1.81/0.98      ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
% 1.81/0.98      | X0_49 = X1_49
% 1.81/0.98      | r2_hidden(X1_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | sP0_iProver_split != iProver_top ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2837,c_1924]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2849,plain,
% 1.81/0.98      ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
% 1.81/0.98      | X0_49 = X1_49
% 1.81/0.98      | r2_hidden(X1_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | v2_funct_1(sK4) = iProver_top ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2824,c_1921]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3243,plain,
% 1.81/0.98      ( r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | r2_hidden(X1_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | X0_49 = X1_49
% 1.81/0.98      | k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49) ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3034,c_2238,c_2849]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3244,plain,
% 1.81/0.98      ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,X1_49)
% 1.81/0.98      | X0_49 = X1_49
% 1.81/0.98      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | r2_hidden(X1_49,k1_xboole_0) != iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_3243]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3253,plain,
% 1.81/0.98      ( k1_funct_1(sK4,X0_49) != k1_funct_1(sK4,sK5)
% 1.81/0.98      | sK6 = X0_49
% 1.81/0.98      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_3177,c_3244]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3387,plain,
% 1.81/0.98      ( sK6 = sK5
% 1.81/0.98      | r2_hidden(sK6,k1_xboole_0) != iProver_top
% 1.81/0.98      | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
% 1.81/0.98      inference(equality_resolution,[status(thm)],[c_3253]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3634,plain,
% 1.81/0.98      ( sK6 = sK5
% 1.81/0.98      | r2_hidden(sK6,k1_xboole_0) != iProver_top
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2850,c_3387]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1644,negated_conjecture,
% 1.81/0.98      ( r2_hidden(sK6,sK2) | ~ v2_funct_1(sK4) ),
% 1.81/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_1919,plain,
% 1.81/0.98      ( r2_hidden(sK6,sK2) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_2851,plain,
% 1.81/0.98      ( r2_hidden(sK6,k1_xboole_0) = iProver_top
% 1.81/0.98      | v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(demodulation,[status(thm)],[c_2824,c_1919]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3799,plain,
% 1.81/0.98      ( v2_funct_1(sK4) != iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3634,c_1682,c_1685,c_2255,c_2850,c_2851,c_3387]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3804,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK1(sK4)) = k1_funct_1(sK4,sK0(sK4)) ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_2400,c_3799]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3811,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_49)
% 1.81/0.98      | sK1(sK4) = X0_49
% 1.81/0.98      | r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | r2_hidden(sK1(sK4),k1_xboole_0) != iProver_top ),
% 1.81/0.98      inference(superposition,[status(thm)],[c_3804,c_3244]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3396,plain,
% 1.81/0.98      ( r2_hidden(sK1(sK4),k1_xboole_0) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3032,c_1682,c_1685,c_2255,c_2850,c_2851,c_3387]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3915,plain,
% 1.81/0.98      ( r2_hidden(X0_49,k1_xboole_0) != iProver_top
% 1.81/0.98      | sK1(sK4) = X0_49
% 1.81/0.98      | k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_49) ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3811,c_1682,c_1685,c_2255,c_2850,c_2851,c_3032,c_3387]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3916,plain,
% 1.81/0.98      ( k1_funct_1(sK4,sK0(sK4)) != k1_funct_1(sK4,X0_49)
% 1.81/0.98      | sK1(sK4) = X0_49
% 1.81/0.98      | r2_hidden(X0_49,k1_xboole_0) != iProver_top ),
% 1.81/0.98      inference(renaming,[status(thm)],[c_3915]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3925,plain,
% 1.81/0.98      ( sK1(sK4) = sK0(sK4)
% 1.81/0.98      | r2_hidden(sK0(sK4),k1_xboole_0) != iProver_top ),
% 1.81/0.98      inference(equality_resolution,[status(thm)],[c_3916]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(c_3541,plain,
% 1.81/0.98      ( r2_hidden(sK0(sK4),k1_xboole_0) = iProver_top ),
% 1.81/0.98      inference(global_propositional_subsumption,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3033,c_1682,c_1685,c_2255,c_2850,c_2851,c_3387]) ).
% 1.81/0.98  
% 1.81/0.98  cnf(contradiction,plain,
% 1.81/0.98      ( $false ),
% 1.81/0.98      inference(minisat,
% 1.81/0.98                [status(thm)],
% 1.81/0.98                [c_3925,c_3799,c_3541,c_2133,c_2110,c_2068,c_1699]) ).
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.81/0.98  
% 1.81/0.98  ------                               Statistics
% 1.81/0.98  
% 1.81/0.98  ------ General
% 1.81/0.98  
% 1.81/0.98  abstr_ref_over_cycles:                  0
% 1.81/0.98  abstr_ref_under_cycles:                 0
% 1.81/0.98  gc_basic_clause_elim:                   0
% 1.81/0.98  forced_gc_time:                         0
% 1.81/0.98  parsing_time:                           0.012
% 1.81/0.98  unif_index_cands_time:                  0.
% 1.81/0.98  unif_index_add_time:                    0.
% 1.81/0.98  orderings_time:                         0.
% 1.81/0.98  out_proof_time:                         0.011
% 1.81/0.98  total_time:                             0.146
% 1.81/0.98  num_of_symbols:                         55
% 1.81/0.98  num_of_terms:                           1653
% 1.81/0.98  
% 1.81/0.98  ------ Preprocessing
% 1.81/0.98  
% 1.81/0.98  num_of_splits:                          1
% 1.81/0.98  num_of_split_atoms:                     1
% 1.81/0.98  num_of_reused_defs:                     0
% 1.81/0.98  num_eq_ax_congr_red:                    5
% 1.81/0.98  num_of_sem_filtered_clauses:            1
% 1.81/0.98  num_of_subtypes:                        4
% 1.81/0.98  monotx_restored_types:                  0
% 1.81/0.98  sat_num_of_epr_types:                   0
% 1.81/0.98  sat_num_of_non_cyclic_types:            0
% 1.81/0.98  sat_guarded_non_collapsed_types:        1
% 1.81/0.98  num_pure_diseq_elim:                    0
% 1.81/0.98  simp_replaced_by:                       0
% 1.81/0.98  res_preprocessed:                       113
% 1.81/0.98  prep_upred:                             0
% 1.81/0.98  prep_unflattend:                        29
% 1.81/0.98  smt_new_axioms:                         0
% 1.81/0.98  pred_elim_cands:                        3
% 1.81/0.98  pred_elim:                              3
% 1.81/0.98  pred_elim_cl:                           6
% 1.81/0.98  pred_elim_cycles:                       5
% 1.81/0.98  merged_defs:                            0
% 1.81/0.98  merged_defs_ncl:                        0
% 1.81/0.98  bin_hyper_res:                          0
% 1.81/0.98  prep_cycles:                            4
% 1.81/0.98  pred_elim_time:                         0.038
% 1.81/0.98  splitting_time:                         0.
% 1.81/0.98  sem_filter_time:                        0.
% 1.81/0.98  monotx_time:                            0.
% 1.81/0.98  subtype_inf_time:                       0.
% 1.81/0.98  
% 1.81/0.98  ------ Problem properties
% 1.81/0.98  
% 1.81/0.98  clauses:                                18
% 1.81/0.98  conjectures:                            6
% 1.81/0.98  epr:                                    5
% 1.81/0.98  horn:                                   12
% 1.81/0.98  ground:                                 13
% 1.81/0.98  unary:                                  1
% 1.81/0.98  binary:                                 7
% 1.81/0.98  lits:                                   50
% 1.81/0.98  lits_eq:                                22
% 1.81/0.98  fd_pure:                                0
% 1.81/0.98  fd_pseudo:                              0
% 1.81/0.98  fd_cond:                                0
% 1.81/0.98  fd_pseudo_cond:                         2
% 1.81/0.98  ac_symbols:                             0
% 1.81/0.98  
% 1.81/0.98  ------ Propositional Solver
% 1.81/0.98  
% 1.81/0.98  prop_solver_calls:                      31
% 1.81/0.98  prop_fast_solver_calls:                 1041
% 1.81/0.98  smt_solver_calls:                       0
% 1.81/0.98  smt_fast_solver_calls:                  0
% 1.81/0.98  prop_num_of_clauses:                    713
% 1.81/0.98  prop_preprocess_simplified:             2955
% 1.81/0.98  prop_fo_subsumed:                       24
% 1.81/0.98  prop_solver_time:                       0.
% 1.81/0.98  smt_solver_time:                        0.
% 1.81/0.98  smt_fast_solver_time:                   0.
% 1.81/0.98  prop_fast_solver_time:                  0.
% 1.81/0.98  prop_unsat_core_time:                   0.
% 1.81/0.98  
% 1.81/0.98  ------ QBF
% 1.81/0.98  
% 1.81/0.98  qbf_q_res:                              0
% 1.81/0.98  qbf_num_tautologies:                    0
% 1.81/0.98  qbf_prep_cycles:                        0
% 1.81/0.98  
% 1.81/0.98  ------ BMC1
% 1.81/0.98  
% 1.81/0.98  bmc1_current_bound:                     -1
% 1.81/0.98  bmc1_last_solved_bound:                 -1
% 1.81/0.98  bmc1_unsat_core_size:                   -1
% 1.81/0.98  bmc1_unsat_core_parents_size:           -1
% 1.81/0.98  bmc1_merge_next_fun:                    0
% 1.81/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.81/0.98  
% 1.81/0.98  ------ Instantiation
% 1.81/0.98  
% 1.81/0.98  inst_num_of_clauses:                    218
% 1.81/0.98  inst_num_in_passive:                    40
% 1.81/0.98  inst_num_in_active:                     177
% 1.81/0.98  inst_num_in_unprocessed:                2
% 1.81/0.98  inst_num_of_loops:                      230
% 1.81/0.98  inst_num_of_learning_restarts:          0
% 1.81/0.98  inst_num_moves_active_passive:          44
% 1.81/0.98  inst_lit_activity:                      0
% 1.81/0.98  inst_lit_activity_moves:                0
% 1.81/0.98  inst_num_tautologies:                   0
% 1.81/0.98  inst_num_prop_implied:                  0
% 1.81/0.98  inst_num_existing_simplified:           0
% 1.81/0.98  inst_num_eq_res_simplified:             0
% 1.81/0.98  inst_num_child_elim:                    0
% 1.81/0.98  inst_num_of_dismatching_blockings:      132
% 1.81/0.98  inst_num_of_non_proper_insts:           390
% 1.81/0.98  inst_num_of_duplicates:                 0
% 1.81/0.98  inst_inst_num_from_inst_to_res:         0
% 1.81/0.98  inst_dismatching_checking_time:         0.
% 1.81/0.98  
% 1.81/0.98  ------ Resolution
% 1.81/0.98  
% 1.81/0.98  res_num_of_clauses:                     0
% 1.81/0.98  res_num_in_passive:                     0
% 1.81/0.98  res_num_in_active:                      0
% 1.81/0.98  res_num_of_loops:                       117
% 1.81/0.98  res_forward_subset_subsumed:            127
% 1.81/0.98  res_backward_subset_subsumed:           2
% 1.81/0.98  res_forward_subsumed:                   0
% 1.81/0.98  res_backward_subsumed:                  0
% 1.81/0.98  res_forward_subsumption_resolution:     0
% 1.81/0.98  res_backward_subsumption_resolution:    0
% 1.81/0.98  res_clause_to_clause_subsumption:       88
% 1.81/0.98  res_orphan_elimination:                 0
% 1.81/0.98  res_tautology_del:                      138
% 1.81/0.98  res_num_eq_res_simplified:              1
% 1.81/0.98  res_num_sel_changes:                    0
% 1.81/0.98  res_moves_from_active_to_pass:          0
% 1.81/0.98  
% 1.81/0.98  ------ Superposition
% 1.81/0.98  
% 1.81/0.98  sup_time_total:                         0.
% 1.81/0.98  sup_time_generating:                    0.
% 1.81/0.98  sup_time_sim_full:                      0.
% 1.81/0.98  sup_time_sim_immed:                     0.
% 1.81/0.98  
% 1.81/0.98  sup_num_of_clauses:                     28
% 1.81/0.98  sup_num_in_active:                      22
% 1.81/0.98  sup_num_in_passive:                     6
% 1.81/0.98  sup_num_of_loops:                       45
% 1.81/0.98  sup_fw_superposition:                   18
% 1.81/0.98  sup_bw_superposition:                   18
% 1.81/0.98  sup_immediate_simplified:               12
% 1.81/0.98  sup_given_eliminated:                   0
% 1.81/0.98  comparisons_done:                       0
% 1.81/0.98  comparisons_avoided:                    9
% 1.81/0.98  
% 1.81/0.98  ------ Simplifications
% 1.81/0.98  
% 1.81/0.98  
% 1.81/0.98  sim_fw_subset_subsumed:                 6
% 1.81/0.98  sim_bw_subset_subsumed:                 12
% 1.81/0.98  sim_fw_subsumed:                        0
% 1.81/0.98  sim_bw_subsumed:                        0
% 1.81/0.98  sim_fw_subsumption_res:                 0
% 1.81/0.98  sim_bw_subsumption_res:                 0
% 1.81/0.98  sim_tautology_del:                      0
% 1.81/0.98  sim_eq_tautology_del:                   12
% 1.81/0.98  sim_eq_res_simp:                        3
% 1.81/0.98  sim_fw_demodulated:                     0
% 1.81/0.98  sim_bw_demodulated:                     20
% 1.81/0.98  sim_light_normalised:                   3
% 1.81/0.98  sim_joinable_taut:                      0
% 1.81/0.98  sim_joinable_simp:                      0
% 1.81/0.98  sim_ac_normalised:                      0
% 1.81/0.98  sim_smt_subsumption:                    0
% 1.81/0.98  
%------------------------------------------------------------------------------
