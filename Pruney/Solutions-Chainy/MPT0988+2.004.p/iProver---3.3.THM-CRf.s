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
% DateTime   : Thu Dec  3 12:02:55 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  148 (1109 expanded)
%              Number of clauses        :   90 ( 322 expanded)
%              Number of leaves         :   13 ( 281 expanded)
%              Depth                    :   23
%              Number of atoms          :  631 (13989 expanded)
%              Number of equality atoms :  320 (6132 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) )
                   => ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) ) )
                  & ( ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) )
                   => ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) ) ) )
              & v2_funct_1(X2)
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) )
                     => ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) ) )
                    & ( ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) )
                     => ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) ) ) )
                & v2_funct_1(X2)
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK4
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5,X4] :
            ( ( ( k1_funct_1(sK4,X4) = X5
                & r2_hidden(X4,X1) )
              | k1_funct_1(X2,X5) != X4
              | ~ r2_hidden(X5,X0) )
            & ( ( k1_funct_1(X2,X5) = X4
                & r2_hidden(X5,X0) )
              | k1_funct_1(sK4,X4) != X5
              | ~ r2_hidden(X4,X1) ) )
        & v2_funct_1(X2)
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & ! [X4,X5] :
                ( ( ( k1_funct_1(X3,X4) = X5
                    & r2_hidden(X4,X1) )
                  | k1_funct_1(X2,X5) != X4
                  | ~ r2_hidden(X5,X0) )
                & ( ( k1_funct_1(X2,X5) = X4
                    & r2_hidden(X5,X0) )
                  | k1_funct_1(X3,X4) != X5
                  | ~ r2_hidden(X4,X1) ) )
            & v2_funct_1(X2)
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & ! [X5,X4] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,sK2) )
                | k1_funct_1(sK3,X5) != X4
                | ~ r2_hidden(X5,sK1) )
              & ( ( k1_funct_1(sK3,X5) = X4
                  & r2_hidden(X5,sK1) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,sK2) ) )
          & v2_funct_1(sK3)
          & k2_relset_1(sK1,sK2,sK3) = sK2
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & ! [X4,X5] :
        ( ( ( k1_funct_1(sK4,X4) = X5
            & r2_hidden(X4,sK2) )
          | k1_funct_1(sK3,X5) != X4
          | ~ r2_hidden(X5,sK1) )
        & ( ( k1_funct_1(sK3,X5) = X4
            & r2_hidden(X5,sK1) )
          | k1_funct_1(sK4,X4) != X5
          | ~ r2_hidden(X4,sK2) ) )
    & v2_funct_1(sK3)
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f34,f33])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | k1_funct_1(sK4,X4) != X5
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK4,X4),sK1)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f70,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK3,X5) = X4
      | k1_funct_1(sK4,X4) != X5
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,k1_funct_1(sK4,X4)) = X4
      | ~ r2_hidden(X4,sK2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_840,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_849,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2284,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2
    | sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_849])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1301,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k1_relset_1(sK2,sK1,sK4) = sK2
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3762,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2284,c_31,c_30,c_23,c_1301])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_856,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1669,plain,
    ( k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_840,c_856])).

cnf(c_3765,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_3762,c_1669])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_841,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_861,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2096,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_861])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_837,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_855,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1560,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_837,c_855])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1562,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1560,c_29])).

cnf(c_2097,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2096,c_1562])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1435,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_0,c_33])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1488,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1435,c_1])).

cnf(c_1489,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_3590,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2097,c_36,c_1489])).

cnf(c_9,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_857,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3595,plain,
    ( k1_relat_1(X0) != sK2
    | k2_funct_1(sK3) = X0
    | r2_hidden(sK0(k2_funct_1(sK3),X0),k1_relat_1(k2_funct_1(sK3))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3590,c_857])).

cnf(c_3625,plain,
    ( k1_relat_1(X0) != sK2
    | k2_funct_1(sK3) = X0
    | r2_hidden(sK0(k2_funct_1(sK3),X0),sK2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3595,c_3590])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_42,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1313,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1456,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1457,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1335,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1459,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_1460,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_1190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1519,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_1526,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_1548,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1549,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1548])).

cnf(c_6612,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | k2_funct_1(sK3) = X0
    | r2_hidden(sK0(k2_funct_1(sK3),X0),sK2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3625,c_36,c_37,c_38,c_29,c_42,c_1457,c_1460,c_1526,c_1549])).

cnf(c_6613,plain,
    ( k1_relat_1(X0) != sK2
    | k2_funct_1(sK3) = X0
    | r2_hidden(sK0(k2_funct_1(sK3),X0),sK2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6612])).

cnf(c_7546,plain,
    ( k2_funct_1(sK3) = sK4
    | r2_hidden(sK0(k2_funct_1(sK3),sK4),sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3765,c_6613])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_21,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1433,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_0,c_30])).

cnf(c_1440,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1433,c_1])).

cnf(c_1441,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1440])).

cnf(c_11383,plain,
    ( r2_hidden(sK0(k2_funct_1(sK3),sK4),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7546,c_39,c_21,c_1441])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_842,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2285,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_849])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1304,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3768,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2285,c_34,c_33,c_22,c_1304])).

cnf(c_1670,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_837,c_856])).

cnf(c_3771,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_3768,c_1670])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_859,plain,
    ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X1)) = X1
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8078,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK1) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3771,c_859])).

cnf(c_9009,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8078,c_36,c_42,c_1489])).

cnf(c_9010,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9009])).

cnf(c_9017,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_842,c_9010])).

cnf(c_11399,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)))) = k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) ),
    inference(superposition,[status(thm)],[c_11383,c_9017])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_843,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11427,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4))) = sK0(k2_funct_1(sK3),sK4) ),
    inference(superposition,[status(thm)],[c_11383,c_843])).

cnf(c_11470,plain,
    ( k1_funct_1(k2_funct_1(sK3),sK0(k2_funct_1(sK3),sK4)) = k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) ),
    inference(light_normalisation,[status(thm)],[c_11399,c_11427])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_858,plain,
    ( X0 = X1
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19545,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4)
    | k2_funct_1(sK3) = sK4
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_11470,c_858])).

cnf(c_19546,plain,
    ( k2_funct_1(sK3) = sK4
    | sK2 != sK2
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19545,c_3590,c_3765])).

cnf(c_19547,plain,
    ( k2_funct_1(sK3) = sK4
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19546])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19547,c_1549,c_1526,c_1460,c_1457,c_1441,c_21,c_42,c_29,c_39,c_38,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:46:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.79/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.79/1.48  
% 7.79/1.48  ------  iProver source info
% 7.79/1.48  
% 7.79/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.79/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.79/1.48  git: non_committed_changes: false
% 7.79/1.48  git: last_make_outside_of_git: false
% 7.79/1.48  
% 7.79/1.48  ------ 
% 7.79/1.48  
% 7.79/1.48  ------ Input Options
% 7.79/1.48  
% 7.79/1.48  --out_options                           all
% 7.79/1.48  --tptp_safe_out                         true
% 7.79/1.48  --problem_path                          ""
% 7.79/1.48  --include_path                          ""
% 7.79/1.48  --clausifier                            res/vclausify_rel
% 7.79/1.48  --clausifier_options                    --mode clausify
% 7.79/1.48  --stdin                                 false
% 7.79/1.48  --stats_out                             sel
% 7.79/1.48  
% 7.79/1.48  ------ General Options
% 7.79/1.48  
% 7.79/1.48  --fof                                   false
% 7.79/1.48  --time_out_real                         604.99
% 7.79/1.48  --time_out_virtual                      -1.
% 7.79/1.48  --symbol_type_check                     false
% 7.79/1.48  --clausify_out                          false
% 7.79/1.48  --sig_cnt_out                           false
% 7.79/1.48  --trig_cnt_out                          false
% 7.79/1.48  --trig_cnt_out_tolerance                1.
% 7.79/1.48  --trig_cnt_out_sk_spl                   false
% 7.79/1.48  --abstr_cl_out                          false
% 7.79/1.48  
% 7.79/1.48  ------ Global Options
% 7.79/1.48  
% 7.79/1.48  --schedule                              none
% 7.79/1.48  --add_important_lit                     false
% 7.79/1.48  --prop_solver_per_cl                    1000
% 7.79/1.48  --min_unsat_core                        false
% 7.79/1.48  --soft_assumptions                      false
% 7.79/1.48  --soft_lemma_size                       3
% 7.79/1.48  --prop_impl_unit_size                   0
% 7.79/1.48  --prop_impl_unit                        []
% 7.79/1.48  --share_sel_clauses                     true
% 7.79/1.48  --reset_solvers                         false
% 7.79/1.48  --bc_imp_inh                            [conj_cone]
% 7.79/1.48  --conj_cone_tolerance                   3.
% 7.79/1.48  --extra_neg_conj                        none
% 7.79/1.48  --large_theory_mode                     true
% 7.79/1.48  --prolific_symb_bound                   200
% 7.79/1.48  --lt_threshold                          2000
% 7.79/1.48  --clause_weak_htbl                      true
% 7.79/1.48  --gc_record_bc_elim                     false
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing Options
% 7.79/1.48  
% 7.79/1.48  --preprocessing_flag                    true
% 7.79/1.48  --time_out_prep_mult                    0.1
% 7.79/1.48  --splitting_mode                        input
% 7.79/1.48  --splitting_grd                         true
% 7.79/1.48  --splitting_cvd                         false
% 7.79/1.48  --splitting_cvd_svl                     false
% 7.79/1.48  --splitting_nvd                         32
% 7.79/1.48  --sub_typing                            true
% 7.79/1.48  --prep_gs_sim                           false
% 7.79/1.48  --prep_unflatten                        true
% 7.79/1.48  --prep_res_sim                          true
% 7.79/1.48  --prep_upred                            true
% 7.79/1.48  --prep_sem_filter                       exhaustive
% 7.79/1.48  --prep_sem_filter_out                   false
% 7.79/1.48  --pred_elim                             false
% 7.79/1.48  --res_sim_input                         true
% 7.79/1.48  --eq_ax_congr_red                       true
% 7.79/1.48  --pure_diseq_elim                       true
% 7.79/1.48  --brand_transform                       false
% 7.79/1.48  --non_eq_to_eq                          false
% 7.79/1.48  --prep_def_merge                        true
% 7.79/1.48  --prep_def_merge_prop_impl              false
% 7.79/1.48  --prep_def_merge_mbd                    true
% 7.79/1.48  --prep_def_merge_tr_red                 false
% 7.79/1.48  --prep_def_merge_tr_cl                  false
% 7.79/1.48  --smt_preprocessing                     true
% 7.79/1.48  --smt_ac_axioms                         fast
% 7.79/1.48  --preprocessed_out                      false
% 7.79/1.48  --preprocessed_stats                    false
% 7.79/1.48  
% 7.79/1.48  ------ Abstraction refinement Options
% 7.79/1.48  
% 7.79/1.48  --abstr_ref                             []
% 7.79/1.48  --abstr_ref_prep                        false
% 7.79/1.48  --abstr_ref_until_sat                   false
% 7.79/1.48  --abstr_ref_sig_restrict                funpre
% 7.79/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.48  --abstr_ref_under                       []
% 7.79/1.48  
% 7.79/1.48  ------ SAT Options
% 7.79/1.48  
% 7.79/1.48  --sat_mode                              false
% 7.79/1.48  --sat_fm_restart_options                ""
% 7.79/1.48  --sat_gr_def                            false
% 7.79/1.48  --sat_epr_types                         true
% 7.79/1.48  --sat_non_cyclic_types                  false
% 7.79/1.48  --sat_finite_models                     false
% 7.79/1.48  --sat_fm_lemmas                         false
% 7.79/1.48  --sat_fm_prep                           false
% 7.79/1.48  --sat_fm_uc_incr                        true
% 7.79/1.48  --sat_out_model                         small
% 7.79/1.48  --sat_out_clauses                       false
% 7.79/1.48  
% 7.79/1.48  ------ QBF Options
% 7.79/1.48  
% 7.79/1.48  --qbf_mode                              false
% 7.79/1.48  --qbf_elim_univ                         false
% 7.79/1.48  --qbf_dom_inst                          none
% 7.79/1.48  --qbf_dom_pre_inst                      false
% 7.79/1.48  --qbf_sk_in                             false
% 7.79/1.48  --qbf_pred_elim                         true
% 7.79/1.48  --qbf_split                             512
% 7.79/1.48  
% 7.79/1.48  ------ BMC1 Options
% 7.79/1.48  
% 7.79/1.48  --bmc1_incremental                      false
% 7.79/1.48  --bmc1_axioms                           reachable_all
% 7.79/1.48  --bmc1_min_bound                        0
% 7.79/1.48  --bmc1_max_bound                        -1
% 7.79/1.48  --bmc1_max_bound_default                -1
% 7.79/1.48  --bmc1_symbol_reachability              true
% 7.79/1.48  --bmc1_property_lemmas                  false
% 7.79/1.48  --bmc1_k_induction                      false
% 7.79/1.48  --bmc1_non_equiv_states                 false
% 7.79/1.48  --bmc1_deadlock                         false
% 7.79/1.48  --bmc1_ucm                              false
% 7.79/1.48  --bmc1_add_unsat_core                   none
% 7.79/1.48  --bmc1_unsat_core_children              false
% 7.79/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.48  --bmc1_out_stat                         full
% 7.79/1.48  --bmc1_ground_init                      false
% 7.79/1.48  --bmc1_pre_inst_next_state              false
% 7.79/1.48  --bmc1_pre_inst_state                   false
% 7.79/1.48  --bmc1_pre_inst_reach_state             false
% 7.79/1.48  --bmc1_out_unsat_core                   false
% 7.79/1.48  --bmc1_aig_witness_out                  false
% 7.79/1.48  --bmc1_verbose                          false
% 7.79/1.48  --bmc1_dump_clauses_tptp                false
% 7.79/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.48  --bmc1_dump_file                        -
% 7.79/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.48  --bmc1_ucm_extend_mode                  1
% 7.79/1.48  --bmc1_ucm_init_mode                    2
% 7.79/1.48  --bmc1_ucm_cone_mode                    none
% 7.79/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.48  --bmc1_ucm_relax_model                  4
% 7.79/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.48  --bmc1_ucm_layered_model                none
% 7.79/1.48  --bmc1_ucm_max_lemma_size               10
% 7.79/1.48  
% 7.79/1.48  ------ AIG Options
% 7.79/1.48  
% 7.79/1.48  --aig_mode                              false
% 7.79/1.48  
% 7.79/1.48  ------ Instantiation Options
% 7.79/1.48  
% 7.79/1.48  --instantiation_flag                    true
% 7.79/1.48  --inst_sos_flag                         false
% 7.79/1.48  --inst_sos_phase                        true
% 7.79/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel_side                     num_symb
% 7.79/1.48  --inst_solver_per_active                1400
% 7.79/1.48  --inst_solver_calls_frac                1.
% 7.79/1.48  --inst_passive_queue_type               priority_queues
% 7.79/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.48  --inst_passive_queues_freq              [25;2]
% 7.79/1.48  --inst_dismatching                      true
% 7.79/1.48  --inst_eager_unprocessed_to_passive     true
% 7.79/1.48  --inst_prop_sim_given                   true
% 7.79/1.48  --inst_prop_sim_new                     false
% 7.79/1.48  --inst_subs_new                         false
% 7.79/1.48  --inst_eq_res_simp                      false
% 7.79/1.48  --inst_subs_given                       false
% 7.79/1.48  --inst_orphan_elimination               true
% 7.79/1.48  --inst_learning_loop_flag               true
% 7.79/1.48  --inst_learning_start                   3000
% 7.79/1.48  --inst_learning_factor                  2
% 7.79/1.48  --inst_start_prop_sim_after_learn       3
% 7.79/1.48  --inst_sel_renew                        solver
% 7.79/1.48  --inst_lit_activity_flag                true
% 7.79/1.48  --inst_restr_to_given                   false
% 7.79/1.48  --inst_activity_threshold               500
% 7.79/1.48  --inst_out_proof                        true
% 7.79/1.48  
% 7.79/1.48  ------ Resolution Options
% 7.79/1.48  
% 7.79/1.48  --resolution_flag                       true
% 7.79/1.48  --res_lit_sel                           adaptive
% 7.79/1.48  --res_lit_sel_side                      none
% 7.79/1.48  --res_ordering                          kbo
% 7.79/1.48  --res_to_prop_solver                    active
% 7.79/1.48  --res_prop_simpl_new                    false
% 7.79/1.48  --res_prop_simpl_given                  true
% 7.79/1.48  --res_passive_queue_type                priority_queues
% 7.79/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.48  --res_passive_queues_freq               [15;5]
% 7.79/1.48  --res_forward_subs                      full
% 7.79/1.48  --res_backward_subs                     full
% 7.79/1.48  --res_forward_subs_resolution           true
% 7.79/1.48  --res_backward_subs_resolution          true
% 7.79/1.48  --res_orphan_elimination                true
% 7.79/1.48  --res_time_limit                        2.
% 7.79/1.48  --res_out_proof                         true
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Options
% 7.79/1.48  
% 7.79/1.48  --superposition_flag                    true
% 7.79/1.48  --sup_passive_queue_type                priority_queues
% 7.79/1.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.48  --sup_passive_queues_freq               [1;4]
% 7.79/1.48  --demod_completeness_check              fast
% 7.79/1.48  --demod_use_ground                      true
% 7.79/1.48  --sup_to_prop_solver                    passive
% 7.79/1.48  --sup_prop_simpl_new                    true
% 7.79/1.48  --sup_prop_simpl_given                  true
% 7.79/1.48  --sup_fun_splitting                     false
% 7.79/1.48  --sup_smt_interval                      50000
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Simplification Setup
% 7.79/1.48  
% 7.79/1.48  --sup_indices_passive                   []
% 7.79/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.48  --sup_full_bw                           [BwDemod]
% 7.79/1.48  --sup_immed_triv                        [TrivRules]
% 7.79/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.48  --sup_immed_bw_main                     []
% 7.79/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.48  
% 7.79/1.48  ------ Combination Options
% 7.79/1.48  
% 7.79/1.48  --comb_res_mult                         3
% 7.79/1.48  --comb_sup_mult                         2
% 7.79/1.48  --comb_inst_mult                        10
% 7.79/1.48  
% 7.79/1.48  ------ Debug Options
% 7.79/1.48  
% 7.79/1.48  --dbg_backtrace                         false
% 7.79/1.48  --dbg_dump_prop_clauses                 false
% 7.79/1.48  --dbg_dump_prop_clauses_file            -
% 7.79/1.48  --dbg_out_stat                          false
% 7.79/1.48  ------ Parsing...
% 7.79/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.79/1.48  ------ Proving...
% 7.79/1.48  ------ Problem Properties 
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  clauses                                 36
% 7.79/1.48  conjectures                             15
% 7.79/1.48  EPR                                     7
% 7.79/1.48  Horn                                    31
% 7.79/1.48  unary                                   12
% 7.79/1.48  binary                                  6
% 7.79/1.48  lits                                    104
% 7.79/1.48  lits eq                                 29
% 7.79/1.48  fd_pure                                 0
% 7.79/1.48  fd_pseudo                               0
% 7.79/1.48  fd_cond                                 3
% 7.79/1.48  fd_pseudo_cond                          2
% 7.79/1.48  AC symbols                              0
% 7.79/1.48  
% 7.79/1.48  ------ Input Options Time Limit: Unbounded
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  ------ 
% 7.79/1.48  Current options:
% 7.79/1.48  ------ 
% 7.79/1.48  
% 7.79/1.48  ------ Input Options
% 7.79/1.48  
% 7.79/1.48  --out_options                           all
% 7.79/1.48  --tptp_safe_out                         true
% 7.79/1.48  --problem_path                          ""
% 7.79/1.48  --include_path                          ""
% 7.79/1.48  --clausifier                            res/vclausify_rel
% 7.79/1.48  --clausifier_options                    --mode clausify
% 7.79/1.48  --stdin                                 false
% 7.79/1.48  --stats_out                             sel
% 7.79/1.48  
% 7.79/1.48  ------ General Options
% 7.79/1.48  
% 7.79/1.48  --fof                                   false
% 7.79/1.48  --time_out_real                         604.99
% 7.79/1.48  --time_out_virtual                      -1.
% 7.79/1.48  --symbol_type_check                     false
% 7.79/1.48  --clausify_out                          false
% 7.79/1.48  --sig_cnt_out                           false
% 7.79/1.48  --trig_cnt_out                          false
% 7.79/1.48  --trig_cnt_out_tolerance                1.
% 7.79/1.48  --trig_cnt_out_sk_spl                   false
% 7.79/1.48  --abstr_cl_out                          false
% 7.79/1.48  
% 7.79/1.48  ------ Global Options
% 7.79/1.48  
% 7.79/1.48  --schedule                              none
% 7.79/1.48  --add_important_lit                     false
% 7.79/1.48  --prop_solver_per_cl                    1000
% 7.79/1.48  --min_unsat_core                        false
% 7.79/1.48  --soft_assumptions                      false
% 7.79/1.48  --soft_lemma_size                       3
% 7.79/1.48  --prop_impl_unit_size                   0
% 7.79/1.48  --prop_impl_unit                        []
% 7.79/1.48  --share_sel_clauses                     true
% 7.79/1.48  --reset_solvers                         false
% 7.79/1.48  --bc_imp_inh                            [conj_cone]
% 7.79/1.48  --conj_cone_tolerance                   3.
% 7.79/1.48  --extra_neg_conj                        none
% 7.79/1.48  --large_theory_mode                     true
% 7.79/1.48  --prolific_symb_bound                   200
% 7.79/1.48  --lt_threshold                          2000
% 7.79/1.48  --clause_weak_htbl                      true
% 7.79/1.48  --gc_record_bc_elim                     false
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing Options
% 7.79/1.48  
% 7.79/1.48  --preprocessing_flag                    true
% 7.79/1.48  --time_out_prep_mult                    0.1
% 7.79/1.48  --splitting_mode                        input
% 7.79/1.48  --splitting_grd                         true
% 7.79/1.48  --splitting_cvd                         false
% 7.79/1.48  --splitting_cvd_svl                     false
% 7.79/1.48  --splitting_nvd                         32
% 7.79/1.48  --sub_typing                            true
% 7.79/1.48  --prep_gs_sim                           false
% 7.79/1.48  --prep_unflatten                        true
% 7.79/1.48  --prep_res_sim                          true
% 7.79/1.48  --prep_upred                            true
% 7.79/1.48  --prep_sem_filter                       exhaustive
% 7.79/1.48  --prep_sem_filter_out                   false
% 7.79/1.48  --pred_elim                             false
% 7.79/1.48  --res_sim_input                         true
% 7.79/1.48  --eq_ax_congr_red                       true
% 7.79/1.48  --pure_diseq_elim                       true
% 7.79/1.48  --brand_transform                       false
% 7.79/1.48  --non_eq_to_eq                          false
% 7.79/1.48  --prep_def_merge                        true
% 7.79/1.48  --prep_def_merge_prop_impl              false
% 7.79/1.48  --prep_def_merge_mbd                    true
% 7.79/1.48  --prep_def_merge_tr_red                 false
% 7.79/1.48  --prep_def_merge_tr_cl                  false
% 7.79/1.48  --smt_preprocessing                     true
% 7.79/1.48  --smt_ac_axioms                         fast
% 7.79/1.48  --preprocessed_out                      false
% 7.79/1.48  --preprocessed_stats                    false
% 7.79/1.48  
% 7.79/1.48  ------ Abstraction refinement Options
% 7.79/1.48  
% 7.79/1.48  --abstr_ref                             []
% 7.79/1.48  --abstr_ref_prep                        false
% 7.79/1.48  --abstr_ref_until_sat                   false
% 7.79/1.48  --abstr_ref_sig_restrict                funpre
% 7.79/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.48  --abstr_ref_under                       []
% 7.79/1.48  
% 7.79/1.48  ------ SAT Options
% 7.79/1.48  
% 7.79/1.48  --sat_mode                              false
% 7.79/1.48  --sat_fm_restart_options                ""
% 7.79/1.48  --sat_gr_def                            false
% 7.79/1.48  --sat_epr_types                         true
% 7.79/1.48  --sat_non_cyclic_types                  false
% 7.79/1.48  --sat_finite_models                     false
% 7.79/1.48  --sat_fm_lemmas                         false
% 7.79/1.48  --sat_fm_prep                           false
% 7.79/1.48  --sat_fm_uc_incr                        true
% 7.79/1.48  --sat_out_model                         small
% 7.79/1.48  --sat_out_clauses                       false
% 7.79/1.48  
% 7.79/1.48  ------ QBF Options
% 7.79/1.48  
% 7.79/1.48  --qbf_mode                              false
% 7.79/1.48  --qbf_elim_univ                         false
% 7.79/1.48  --qbf_dom_inst                          none
% 7.79/1.48  --qbf_dom_pre_inst                      false
% 7.79/1.48  --qbf_sk_in                             false
% 7.79/1.48  --qbf_pred_elim                         true
% 7.79/1.48  --qbf_split                             512
% 7.79/1.48  
% 7.79/1.48  ------ BMC1 Options
% 7.79/1.48  
% 7.79/1.48  --bmc1_incremental                      false
% 7.79/1.48  --bmc1_axioms                           reachable_all
% 7.79/1.48  --bmc1_min_bound                        0
% 7.79/1.48  --bmc1_max_bound                        -1
% 7.79/1.48  --bmc1_max_bound_default                -1
% 7.79/1.48  --bmc1_symbol_reachability              true
% 7.79/1.48  --bmc1_property_lemmas                  false
% 7.79/1.48  --bmc1_k_induction                      false
% 7.79/1.48  --bmc1_non_equiv_states                 false
% 7.79/1.48  --bmc1_deadlock                         false
% 7.79/1.48  --bmc1_ucm                              false
% 7.79/1.48  --bmc1_add_unsat_core                   none
% 7.79/1.48  --bmc1_unsat_core_children              false
% 7.79/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.48  --bmc1_out_stat                         full
% 7.79/1.48  --bmc1_ground_init                      false
% 7.79/1.48  --bmc1_pre_inst_next_state              false
% 7.79/1.48  --bmc1_pre_inst_state                   false
% 7.79/1.48  --bmc1_pre_inst_reach_state             false
% 7.79/1.48  --bmc1_out_unsat_core                   false
% 7.79/1.48  --bmc1_aig_witness_out                  false
% 7.79/1.48  --bmc1_verbose                          false
% 7.79/1.48  --bmc1_dump_clauses_tptp                false
% 7.79/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.48  --bmc1_dump_file                        -
% 7.79/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.48  --bmc1_ucm_extend_mode                  1
% 7.79/1.48  --bmc1_ucm_init_mode                    2
% 7.79/1.48  --bmc1_ucm_cone_mode                    none
% 7.79/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.48  --bmc1_ucm_relax_model                  4
% 7.79/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.48  --bmc1_ucm_layered_model                none
% 7.79/1.48  --bmc1_ucm_max_lemma_size               10
% 7.79/1.48  
% 7.79/1.48  ------ AIG Options
% 7.79/1.48  
% 7.79/1.48  --aig_mode                              false
% 7.79/1.48  
% 7.79/1.48  ------ Instantiation Options
% 7.79/1.48  
% 7.79/1.48  --instantiation_flag                    true
% 7.79/1.48  --inst_sos_flag                         false
% 7.79/1.48  --inst_sos_phase                        true
% 7.79/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel_side                     num_symb
% 7.79/1.48  --inst_solver_per_active                1400
% 7.79/1.48  --inst_solver_calls_frac                1.
% 7.79/1.48  --inst_passive_queue_type               priority_queues
% 7.79/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.48  --inst_passive_queues_freq              [25;2]
% 7.79/1.48  --inst_dismatching                      true
% 7.79/1.48  --inst_eager_unprocessed_to_passive     true
% 7.79/1.48  --inst_prop_sim_given                   true
% 7.79/1.48  --inst_prop_sim_new                     false
% 7.79/1.48  --inst_subs_new                         false
% 7.79/1.48  --inst_eq_res_simp                      false
% 7.79/1.48  --inst_subs_given                       false
% 7.79/1.48  --inst_orphan_elimination               true
% 7.79/1.48  --inst_learning_loop_flag               true
% 7.79/1.48  --inst_learning_start                   3000
% 7.79/1.48  --inst_learning_factor                  2
% 7.79/1.48  --inst_start_prop_sim_after_learn       3
% 7.79/1.48  --inst_sel_renew                        solver
% 7.79/1.48  --inst_lit_activity_flag                true
% 7.79/1.48  --inst_restr_to_given                   false
% 7.79/1.48  --inst_activity_threshold               500
% 7.79/1.48  --inst_out_proof                        true
% 7.79/1.48  
% 7.79/1.48  ------ Resolution Options
% 7.79/1.48  
% 7.79/1.48  --resolution_flag                       true
% 7.79/1.48  --res_lit_sel                           adaptive
% 7.79/1.48  --res_lit_sel_side                      none
% 7.79/1.48  --res_ordering                          kbo
% 7.79/1.48  --res_to_prop_solver                    active
% 7.79/1.48  --res_prop_simpl_new                    false
% 7.79/1.48  --res_prop_simpl_given                  true
% 7.79/1.48  --res_passive_queue_type                priority_queues
% 7.79/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.48  --res_passive_queues_freq               [15;5]
% 7.79/1.48  --res_forward_subs                      full
% 7.79/1.48  --res_backward_subs                     full
% 7.79/1.48  --res_forward_subs_resolution           true
% 7.79/1.48  --res_backward_subs_resolution          true
% 7.79/1.48  --res_orphan_elimination                true
% 7.79/1.48  --res_time_limit                        2.
% 7.79/1.48  --res_out_proof                         true
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Options
% 7.79/1.48  
% 7.79/1.48  --superposition_flag                    true
% 7.79/1.48  --sup_passive_queue_type                priority_queues
% 7.79/1.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.48  --sup_passive_queues_freq               [1;4]
% 7.79/1.48  --demod_completeness_check              fast
% 7.79/1.48  --demod_use_ground                      true
% 7.79/1.48  --sup_to_prop_solver                    passive
% 7.79/1.48  --sup_prop_simpl_new                    true
% 7.79/1.48  --sup_prop_simpl_given                  true
% 7.79/1.48  --sup_fun_splitting                     false
% 7.79/1.48  --sup_smt_interval                      50000
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Simplification Setup
% 7.79/1.48  
% 7.79/1.48  --sup_indices_passive                   []
% 7.79/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.48  --sup_full_bw                           [BwDemod]
% 7.79/1.48  --sup_immed_triv                        [TrivRules]
% 7.79/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.48  --sup_immed_bw_main                     []
% 7.79/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.48  
% 7.79/1.48  ------ Combination Options
% 7.79/1.48  
% 7.79/1.48  --comb_res_mult                         3
% 7.79/1.48  --comb_sup_mult                         2
% 7.79/1.48  --comb_inst_mult                        10
% 7.79/1.48  
% 7.79/1.48  ------ Debug Options
% 7.79/1.48  
% 7.79/1.48  --dbg_backtrace                         false
% 7.79/1.48  --dbg_dump_prop_clauses                 false
% 7.79/1.48  --dbg_dump_prop_clauses_file            -
% 7.79/1.48  --dbg_out_stat                          false
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  ------ Proving...
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  % SZS status Theorem for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  fof(f11,conjecture,(
% 7.79/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f12,negated_conjecture,(
% 7.79/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.79/1.48    inference(negated_conjecture,[],[f11])).
% 7.79/1.48  
% 7.79/1.48  fof(f28,plain,(
% 7.79/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | (k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0))) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | (k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.79/1.48    inference(ennf_transformation,[],[f12])).
% 7.79/1.48  
% 7.79/1.48  fof(f29,plain,(
% 7.79/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.79/1.48    inference(flattening,[],[f28])).
% 7.79/1.48  
% 7.79/1.48  fof(f34,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5,X4] : (((k1_funct_1(sK4,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f33,plain,(
% 7.79/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK2)) | k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK1)) & ((k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK1)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK2))) & v2_funct_1(sK3) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f35,plain,(
% 7.79/1.48    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X4,X5] : (((k1_funct_1(sK4,X4) = X5 & r2_hidden(X4,sK2)) | k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK1)) & ((k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK1)) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2))) & v2_funct_1(sK3) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f29,f34,f33])).
% 7.79/1.48  
% 7.79/1.48  fof(f62,plain,(
% 7.79/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f9,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f24,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f9])).
% 7.79/1.48  
% 7.79/1.48  fof(f25,plain,(
% 7.79/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(flattening,[],[f24])).
% 7.79/1.48  
% 7.79/1.48  fof(f32,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(nnf_transformation,[],[f25])).
% 7.79/1.48  
% 7.79/1.48  fof(f48,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f32])).
% 7.79/1.48  
% 7.79/1.48  fof(f61,plain,(
% 7.79/1.48    v1_funct_2(sK4,sK2,sK1)),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f69,plain,(
% 7.79/1.48    k1_xboole_0 != sK1),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f7,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f22,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f7])).
% 7.79/1.48  
% 7.79/1.48  fof(f46,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f22])).
% 7.79/1.48  
% 7.79/1.48  fof(f64,plain,(
% 7.79/1.48    v2_funct_1(sK3)),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f4,axiom,(
% 7.79/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f16,plain,(
% 7.79/1.48    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.79/1.48    inference(ennf_transformation,[],[f4])).
% 7.79/1.48  
% 7.79/1.48  fof(f17,plain,(
% 7.79/1.48    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(flattening,[],[f16])).
% 7.79/1.48  
% 7.79/1.48  fof(f40,plain,(
% 7.79/1.48    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f17])).
% 7.79/1.48  
% 7.79/1.48  fof(f59,plain,(
% 7.79/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f8,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f23,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f8])).
% 7.79/1.48  
% 7.79/1.48  fof(f47,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f23])).
% 7.79/1.48  
% 7.79/1.48  fof(f63,plain,(
% 7.79/1.48    k2_relset_1(sK1,sK2,sK3) = sK2),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f57,plain,(
% 7.79/1.48    v1_funct_1(sK3)),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f1,axiom,(
% 7.79/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f13,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(ennf_transformation,[],[f1])).
% 7.79/1.48  
% 7.79/1.48  fof(f36,plain,(
% 7.79/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f13])).
% 7.79/1.48  
% 7.79/1.48  fof(f2,axiom,(
% 7.79/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f37,plain,(
% 7.79/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f2])).
% 7.79/1.48  
% 7.79/1.48  fof(f6,axiom,(
% 7.79/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f20,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.79/1.48    inference(ennf_transformation,[],[f6])).
% 7.79/1.48  
% 7.79/1.48  fof(f21,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(flattening,[],[f20])).
% 7.79/1.48  
% 7.79/1.48  fof(f30,plain,(
% 7.79/1.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f31,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f30])).
% 7.79/1.48  
% 7.79/1.48  fof(f44,plain,(
% 7.79/1.48    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f31])).
% 7.79/1.48  
% 7.79/1.48  fof(f58,plain,(
% 7.79/1.48    v1_funct_2(sK3,sK1,sK2)),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f10,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f26,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.79/1.48    inference(ennf_transformation,[],[f10])).
% 7.79/1.48  
% 7.79/1.48  fof(f27,plain,(
% 7.79/1.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.79/1.48    inference(flattening,[],[f26])).
% 7.79/1.48  
% 7.79/1.48  fof(f54,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f27])).
% 7.79/1.48  
% 7.79/1.48  fof(f56,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f27])).
% 7.79/1.48  
% 7.79/1.48  fof(f60,plain,(
% 7.79/1.48    v1_funct_1(sK4)),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f71,plain,(
% 7.79/1.48    k2_funct_1(sK3) != sK4),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f65,plain,(
% 7.79/1.48    ( ! [X4,X5] : (r2_hidden(X5,sK1) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f80,plain,(
% 7.79/1.48    ( ! [X4] : (r2_hidden(k1_funct_1(sK4,X4),sK1) | ~r2_hidden(X4,sK2)) )),
% 7.79/1.48    inference(equality_resolution,[],[f65])).
% 7.79/1.48  
% 7.79/1.48  fof(f70,plain,(
% 7.79/1.48    k1_xboole_0 != sK2),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f5,axiom,(
% 7.79/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 7.79/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f18,plain,(
% 7.79/1.48    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.79/1.48    inference(ennf_transformation,[],[f5])).
% 7.79/1.48  
% 7.79/1.48  fof(f19,plain,(
% 7.79/1.48    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.79/1.48    inference(flattening,[],[f18])).
% 7.79/1.48  
% 7.79/1.48  fof(f42,plain,(
% 7.79/1.48    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f19])).
% 7.79/1.48  
% 7.79/1.48  fof(f66,plain,(
% 7.79/1.48    ( ! [X4,X5] : (k1_funct_1(sK3,X5) = X4 | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f79,plain,(
% 7.79/1.48    ( ! [X4] : (k1_funct_1(sK3,k1_funct_1(sK4,X4)) = X4 | ~r2_hidden(X4,sK2)) )),
% 7.79/1.48    inference(equality_resolution,[],[f66])).
% 7.79/1.48  
% 7.79/1.48  fof(f45,plain,(
% 7.79/1.48    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f31])).
% 7.79/1.48  
% 7.79/1.48  cnf(c_30,negated_conjecture,
% 7.79/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.79/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_840,plain,
% 7.79/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_17,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.79/1.48      | k1_xboole_0 = X2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_849,plain,
% 7.79/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.79/1.48      | k1_xboole_0 = X1
% 7.79/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2284,plain,
% 7.79/1.48      ( k1_relset_1(sK2,sK1,sK4) = sK2
% 7.79/1.48      | sK1 = k1_xboole_0
% 7.79/1.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_840,c_849]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_31,negated_conjecture,
% 7.79/1.48      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_23,negated_conjecture,
% 7.79/1.48      ( k1_xboole_0 != sK1 ),
% 7.79/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1301,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.79/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.79/1.48      | k1_relset_1(sK2,sK1,sK4) = sK2
% 7.79/1.48      | k1_xboole_0 = sK1 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3762,plain,
% 7.79/1.48      ( k1_relset_1(sK2,sK1,sK4) = sK2 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_2284,c_31,c_30,c_23,c_1301]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_10,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_856,plain,
% 7.79/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1669,plain,
% 7.79/1.48      ( k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_840,c_856]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3765,plain,
% 7.79/1.48      ( k1_relat_1(sK4) = sK2 ),
% 7.79/1.48      inference(demodulation,[status(thm)],[c_3762,c_1669]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_28,negated_conjecture,
% 7.79/1.48      ( v2_funct_1(sK3) ),
% 7.79/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_841,plain,
% 7.79/1.48      ( v2_funct_1(sK3) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_5,plain,
% 7.79/1.48      ( ~ v2_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f40]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_861,plain,
% 7.79/1.48      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.79/1.48      | v2_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2096,plain,
% 7.79/1.48      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_841,c_861]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_33,negated_conjecture,
% 7.79/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.79/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_837,plain,
% 7.79/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_855,plain,
% 7.79/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1560,plain,
% 7.79/1.48      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_837,c_855]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_29,negated_conjecture,
% 7.79/1.48      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1562,plain,
% 7.79/1.48      ( k2_relat_1(sK3) = sK2 ),
% 7.79/1.48      inference(light_normalisation,[status(thm)],[c_1560,c_29]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2097,plain,
% 7.79/1.48      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.48      inference(light_normalisation,[status(thm)],[c_2096,c_1562]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_35,negated_conjecture,
% 7.79/1.48      ( v1_funct_1(sK3) ),
% 7.79/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_36,plain,
% 7.79/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_0,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.79/1.48      | ~ v1_relat_1(X1)
% 7.79/1.48      | v1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1435,plain,
% 7.79/1.48      ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) | v1_relat_1(sK3) ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_0,c_33]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.79/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1488,plain,
% 7.79/1.48      ( v1_relat_1(sK3) ),
% 7.79/1.48      inference(forward_subsumption_resolution,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_1435,c_1]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1489,plain,
% 7.79/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3590,plain,
% 7.79/1.48      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_2097,c_36,c_1489]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_9,plain,
% 7.79/1.48      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X1)
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | ~ v1_relat_1(X1)
% 7.79/1.48      | X0 = X1
% 7.79/1.48      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_857,plain,
% 7.79/1.48      ( X0 = X1
% 7.79/1.48      | k1_relat_1(X1) != k1_relat_1(X0)
% 7.79/1.48      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(X1) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3595,plain,
% 7.79/1.48      ( k1_relat_1(X0) != sK2
% 7.79/1.48      | k2_funct_1(sK3) = X0
% 7.79/1.48      | r2_hidden(sK0(k2_funct_1(sK3),X0),k1_relat_1(k2_funct_1(sK3))) = iProver_top
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_3590,c_857]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3625,plain,
% 7.79/1.48      ( k1_relat_1(X0) != sK2
% 7.79/1.48      | k2_funct_1(sK3) = X0
% 7.79/1.48      | r2_hidden(sK0(k2_funct_1(sK3),X0),sK2) = iProver_top
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.79/1.48      inference(light_normalisation,[status(thm)],[c_3595,c_3590]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_34,negated_conjecture,
% 7.79/1.48      ( v1_funct_2(sK3,sK1,sK2) ),
% 7.79/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_37,plain,
% 7.79/1.48      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_38,plain,
% 7.79/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_42,plain,
% 7.79/1.48      ( v2_funct_1(sK3) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_20,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | ~ v2_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | v1_funct_1(k2_funct_1(X0))
% 7.79/1.48      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1313,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK3,X0,X1)
% 7.79/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | ~ v2_funct_1(sK3)
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK3))
% 7.79/1.48      | ~ v1_funct_1(sK3)
% 7.79/1.48      | k2_relset_1(X0,X1,sK3) != X1 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1456,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.79/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.79/1.48      | ~ v2_funct_1(sK3)
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK3))
% 7.79/1.48      | ~ v1_funct_1(sK3)
% 7.79/1.48      | k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1313]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1457,plain,
% 7.79/1.48      ( k2_relset_1(sK1,sK2,sK3) != sK2
% 7.79/1.48      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.79/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.79/1.48      | v2_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_18,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.79/1.48      | ~ v2_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1335,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK3,X0,X1)
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.79/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | ~ v2_funct_1(sK3)
% 7.79/1.48      | ~ v1_funct_1(sK3)
% 7.79/1.48      | k2_relset_1(X0,X1,sK3) != X1 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1459,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.79/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.79/1.48      | ~ v2_funct_1(sK3)
% 7.79/1.48      | ~ v1_funct_1(sK3)
% 7.79/1.48      | k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1335]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1460,plain,
% 7.79/1.48      ( k2_relset_1(sK1,sK2,sK3) != sK2
% 7.79/1.48      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 7.79/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.79/1.48      | v2_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1190,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | v1_relat_1(X0)
% 7.79/1.48      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1519,plain,
% 7.79/1.48      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.79/1.48      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK3)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1190]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1526,plain,
% 7.79/1.48      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1519]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1548,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1549,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1548]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_6612,plain,
% 7.79/1.48      ( v1_relat_1(X0) != iProver_top
% 7.79/1.48      | k1_relat_1(X0) != sK2
% 7.79/1.48      | k2_funct_1(sK3) = X0
% 7.79/1.48      | r2_hidden(sK0(k2_funct_1(sK3),X0),sK2) = iProver_top
% 7.79/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3625,c_36,c_37,c_38,c_29,c_42,c_1457,c_1460,c_1526,
% 7.79/1.48                 c_1549]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_6613,plain,
% 7.79/1.48      ( k1_relat_1(X0) != sK2
% 7.79/1.48      | k2_funct_1(sK3) = X0
% 7.79/1.48      | r2_hidden(sK0(k2_funct_1(sK3),X0),sK2) = iProver_top
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.48      inference(renaming,[status(thm)],[c_6612]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_7546,plain,
% 7.79/1.48      ( k2_funct_1(sK3) = sK4
% 7.79/1.48      | r2_hidden(sK0(k2_funct_1(sK3),sK4),sK2) = iProver_top
% 7.79/1.48      | v1_funct_1(sK4) != iProver_top
% 7.79/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_3765,c_6613]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_32,negated_conjecture,
% 7.79/1.48      ( v1_funct_1(sK4) ),
% 7.79/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_39,plain,
% 7.79/1.48      ( v1_funct_1(sK4) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_21,negated_conjecture,
% 7.79/1.48      ( k2_funct_1(sK3) != sK4 ),
% 7.79/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1433,plain,
% 7.79/1.48      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1)) | v1_relat_1(sK4) ),
% 7.79/1.48      inference(resolution,[status(thm)],[c_0,c_30]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1440,plain,
% 7.79/1.48      ( v1_relat_1(sK4) ),
% 7.79/1.48      inference(forward_subsumption_resolution,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_1433,c_1]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1441,plain,
% 7.79/1.48      ( v1_relat_1(sK4) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1440]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11383,plain,
% 7.79/1.48      ( r2_hidden(sK0(k2_funct_1(sK3),sK4),sK2) = iProver_top ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_7546,c_39,c_21,c_1441]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_27,negated_conjecture,
% 7.79/1.48      ( ~ r2_hidden(X0,sK2) | r2_hidden(k1_funct_1(sK4,X0),sK1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_842,plain,
% 7.79/1.48      ( r2_hidden(X0,sK2) != iProver_top
% 7.79/1.48      | r2_hidden(k1_funct_1(sK4,X0),sK1) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2285,plain,
% 7.79/1.48      ( k1_relset_1(sK1,sK2,sK3) = sK1
% 7.79/1.48      | sK2 = k1_xboole_0
% 7.79/1.48      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_837,c_849]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_22,negated_conjecture,
% 7.79/1.48      ( k1_xboole_0 != sK2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1304,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.79/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.79/1.48      | k1_relset_1(sK1,sK2,sK3) = sK1
% 7.79/1.48      | k1_xboole_0 = sK2 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3768,plain,
% 7.79/1.48      ( k1_relset_1(sK1,sK2,sK3) = sK1 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_2285,c_34,c_33,c_22,c_1304]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1670,plain,
% 7.79/1.48      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_837,c_856]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3771,plain,
% 7.79/1.48      ( k1_relat_1(sK3) = sK1 ),
% 7.79/1.48      inference(demodulation,[status(thm)],[c_3768,c_1670]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_7,plain,
% 7.79/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.79/1.48      | ~ v2_funct_1(X1)
% 7.79/1.48      | ~ v1_funct_1(X1)
% 7.79/1.48      | ~ v1_relat_1(X1)
% 7.79/1.48      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 7.79/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_859,plain,
% 7.79/1.48      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X1)) = X1
% 7.79/1.48      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 7.79/1.48      | v2_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_8078,plain,
% 7.79/1.48      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 7.79/1.48      | r2_hidden(X0,sK1) != iProver_top
% 7.79/1.48      | v2_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_3771,c_859]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_9009,plain,
% 7.79/1.48      ( r2_hidden(X0,sK1) != iProver_top
% 7.79/1.48      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_8078,c_36,c_42,c_1489]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_9010,plain,
% 7.79/1.48      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 7.79/1.48      | r2_hidden(X0,sK1) != iProver_top ),
% 7.79/1.48      inference(renaming,[status(thm)],[c_9009]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_9017,plain,
% 7.79/1.48      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
% 7.79/1.48      | r2_hidden(X0,sK2) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_842,c_9010]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11399,plain,
% 7.79/1.48      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)))) = k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_11383,c_9017]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_26,negated_conjecture,
% 7.79/1.48      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0 ),
% 7.79/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_843,plain,
% 7.79/1.48      ( k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0
% 7.79/1.48      | r2_hidden(X0,sK2) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11427,plain,
% 7.79/1.48      ( k1_funct_1(sK3,k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4))) = sK0(k2_funct_1(sK3),sK4) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_11383,c_843]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11470,plain,
% 7.79/1.48      ( k1_funct_1(k2_funct_1(sK3),sK0(k2_funct_1(sK3),sK4)) = k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) ),
% 7.79/1.48      inference(light_normalisation,[status(thm)],[c_11399,c_11427]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_8,plain,
% 7.79/1.48      ( ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X1)
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | ~ v1_relat_1(X1)
% 7.79/1.48      | X0 = X1
% 7.79/1.48      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 7.79/1.48      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_858,plain,
% 7.79/1.48      ( X0 = X1
% 7.79/1.48      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 7.79/1.48      | k1_relat_1(X1) != k1_relat_1(X0)
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(X1) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_19545,plain,
% 7.79/1.48      ( k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4)
% 7.79/1.48      | k2_funct_1(sK3) = sK4
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.79/1.48      | v1_funct_1(sK4) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_11470,c_858]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_19546,plain,
% 7.79/1.48      ( k2_funct_1(sK3) = sK4
% 7.79/1.48      | sK2 != sK2
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.79/1.48      | v1_funct_1(sK4) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.79/1.48      inference(light_normalisation,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_19545,c_3590,c_3765]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_19547,plain,
% 7.79/1.48      ( k2_funct_1(sK3) = sK4
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.79/1.48      | v1_funct_1(sK4) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.79/1.48      inference(equality_resolution_simp,[status(thm)],[c_19546]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(contradiction,plain,
% 7.79/1.48      ( $false ),
% 7.79/1.48      inference(minisat,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_19547,c_1549,c_1526,c_1460,c_1457,c_1441,c_21,c_42,
% 7.79/1.48                 c_29,c_39,c_38,c_37,c_36]) ).
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  ------                               Statistics
% 7.79/1.48  
% 7.79/1.48  ------ Selected
% 7.79/1.48  
% 7.79/1.48  total_time:                             0.655
% 7.79/1.48  
%------------------------------------------------------------------------------
