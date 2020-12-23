%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:56 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :  166 (1189 expanded)
%              Number of clauses        :  108 ( 383 expanded)
%              Number of leaves         :   16 ( 306 expanded)
%              Depth                    :   21
%              Number of atoms          :  709 (14962 expanded)
%              Number of equality atoms :  351 (6506 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f31,f30])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
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

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK1)
      | k1_funct_1(sK4,X4) != X5
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK4,X4),sK1)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK3,X5) = X4
      | k1_funct_1(sK4,X4) != X5
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X4] :
      ( k1_funct_1(sK3,k1_funct_1(sK4,X4)) = X4
      | ~ r2_hidden(X4,sK2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1191,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1196,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3445,plain,
    ( k1_relset_1(sK2,sK1,sK4) = sK2
    | sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1196])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1203,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2194,plain,
    ( k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1191,c_1203])).

cnf(c_3458,plain,
    ( k1_relat_1(sK4) = sK2
    | sK1 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3445,c_2194])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_37,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_677,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_706,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_678,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1496,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_1497,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_6251,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3458,c_37,c_20,c_706,c_1497])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1188,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1202,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2106,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1188,c_1202])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2108,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2106,c_26])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_429,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_430,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_432,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_32])).

cnf(c_1181,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_2113,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2108,c_1181])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1834,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2078,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2079,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2078])).

cnf(c_2656,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2113,c_35,c_1834,c_2079])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1204,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3575,plain,
    ( k1_relat_1(X0) != sK2
    | k2_funct_1(sK3) = X0
    | r2_hidden(sK0(X0,k2_funct_1(sK3)),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_1204])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_357,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_358,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_362,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK3,X0,X1)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_32])).

cnf(c_363,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK3))
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_1435,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_funct_1(k2_funct_1(sK3))
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_1436,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_405,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_406,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_410,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK3,X0,X1)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_32])).

cnf(c_411,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_1451,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_1452,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_1836,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1837,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1836])).

cnf(c_2075,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2076,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2075])).

cnf(c_4420,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK2
    | k2_funct_1(sK3) = X0
    | r2_hidden(sK0(X0,k2_funct_1(sK3)),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3575,c_34,c_35,c_26,c_1436,c_1452,c_1837,c_2076])).

cnf(c_4421,plain,
    ( k1_relat_1(X0) != sK2
    | k2_funct_1(sK3) = X0
    | r2_hidden(sK0(X0,k2_funct_1(sK3)),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4420])).

cnf(c_6257,plain,
    ( k2_funct_1(sK3) = sK4
    | r2_hidden(sK0(sK4,k2_funct_1(sK3)),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6251,c_4421])).

cnf(c_6278,plain,
    ( k2_funct_1(sK3) = sK4
    | r2_hidden(sK0(sK4,k2_funct_1(sK3)),sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6257,c_6251])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_18,negated_conjecture,
    ( k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1830,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1831,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1830])).

cnf(c_16863,plain,
    ( r2_hidden(sK0(sK4,k2_funct_1(sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6278,c_36,c_38,c_18,c_1831,c_2076])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1192,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_330,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_331,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_335,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK3,X0,X1)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_32])).

cnf(c_336,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X2)) = X2
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_335])).

cnf(c_1185,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(sK3,X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_3404,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1185])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1494,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_1495,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_4052,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3404,c_34,c_19,c_706,c_1495])).

cnf(c_4060,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_4052])).

cnf(c_16943,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3))))) = k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3))) ),
    inference(superposition,[status(thm)],[c_16863,c_4060])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1193,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16952,plain,
    ( k1_funct_1(sK3,k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3)))) = sK0(sK4,k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_16863,c_1193])).

cnf(c_16963,plain,
    ( k1_funct_1(k2_funct_1(sK3),sK0(sK4,k2_funct_1(sK3))) = k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3))) ),
    inference(light_normalisation,[status(thm)],[c_16943,c_16952])).

cnf(c_15044,plain,
    ( sK0(k2_funct_1(sK3),sK4) = sK0(k2_funct_1(sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_687,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
    theory(equality)).

cnf(c_12732,plain,
    ( k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) = k1_funct_1(k2_funct_1(sK3),sK0(k2_funct_1(sK3),sK4))
    | sK0(k2_funct_1(sK3),sK4) != sK0(k2_funct_1(sK3),sK4)
    | sK4 != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_3478,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != X0
    | k1_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK4)
    | k1_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_7859,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k1_relat_1(sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_3478])).

cnf(c_2301,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != X0
    | k1_relat_1(sK4) != X0
    | k1_relat_1(sK4) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_7861,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK2
    | k1_relat_1(sK4) = k1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(sK4) != sK2 ),
    inference(instantiation,[status(thm)],[c_2301])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1663,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(X0,sK0(sK4,X0)) != k1_funct_1(sK4,sK0(sK4,X0))
    | k1_relat_1(X0) != k1_relat_1(sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2652,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(k2_funct_1(sK3),sK0(sK4,k2_funct_1(sK3))) != k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3)))
    | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4)
    | sK4 = k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_1559,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) != k1_funct_1(k2_funct_1(sK3),sK0(k2_funct_1(sK3),sK4))
    | k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1560,plain,
    ( k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) != k1_funct_1(k2_funct_1(sK3),sK0(k2_funct_1(sK3),sK4))
    | k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) = sK4
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16963,c_15044,c_12732,c_7859,c_7861,c_3458,c_2652,c_2113,c_2079,c_2076,c_2075,c_1837,c_1836,c_1834,c_1831,c_1830,c_1560,c_1497,c_1452,c_1451,c_1436,c_1435,c_706,c_18,c_20,c_26,c_38,c_27,c_37,c_36,c_29,c_35,c_30,c_34,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.01/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/1.49  
% 7.01/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.01/1.49  
% 7.01/1.49  ------  iProver source info
% 7.01/1.49  
% 7.01/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.01/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.01/1.49  git: non_committed_changes: false
% 7.01/1.49  git: last_make_outside_of_git: false
% 7.01/1.49  
% 7.01/1.49  ------ 
% 7.01/1.49  
% 7.01/1.49  ------ Input Options
% 7.01/1.49  
% 7.01/1.49  --out_options                           all
% 7.01/1.49  --tptp_safe_out                         true
% 7.01/1.49  --problem_path                          ""
% 7.01/1.49  --include_path                          ""
% 7.01/1.49  --clausifier                            res/vclausify_rel
% 7.01/1.49  --clausifier_options                    --mode clausify
% 7.01/1.49  --stdin                                 false
% 7.01/1.49  --stats_out                             all
% 7.01/1.49  
% 7.01/1.49  ------ General Options
% 7.01/1.49  
% 7.01/1.49  --fof                                   false
% 7.01/1.49  --time_out_real                         305.
% 7.01/1.49  --time_out_virtual                      -1.
% 7.01/1.49  --symbol_type_check                     false
% 7.01/1.49  --clausify_out                          false
% 7.01/1.49  --sig_cnt_out                           false
% 7.01/1.49  --trig_cnt_out                          false
% 7.01/1.49  --trig_cnt_out_tolerance                1.
% 7.01/1.49  --trig_cnt_out_sk_spl                   false
% 7.01/1.49  --abstr_cl_out                          false
% 7.01/1.49  
% 7.01/1.49  ------ Global Options
% 7.01/1.49  
% 7.01/1.49  --schedule                              default
% 7.01/1.49  --add_important_lit                     false
% 7.01/1.49  --prop_solver_per_cl                    1000
% 7.01/1.49  --min_unsat_core                        false
% 7.01/1.49  --soft_assumptions                      false
% 7.01/1.49  --soft_lemma_size                       3
% 7.01/1.49  --prop_impl_unit_size                   0
% 7.01/1.49  --prop_impl_unit                        []
% 7.01/1.49  --share_sel_clauses                     true
% 7.01/1.49  --reset_solvers                         false
% 7.01/1.49  --bc_imp_inh                            [conj_cone]
% 7.01/1.49  --conj_cone_tolerance                   3.
% 7.01/1.49  --extra_neg_conj                        none
% 7.01/1.49  --large_theory_mode                     true
% 7.01/1.49  --prolific_symb_bound                   200
% 7.01/1.49  --lt_threshold                          2000
% 7.01/1.49  --clause_weak_htbl                      true
% 7.01/1.49  --gc_record_bc_elim                     false
% 7.01/1.49  
% 7.01/1.49  ------ Preprocessing Options
% 7.01/1.49  
% 7.01/1.49  --preprocessing_flag                    true
% 7.01/1.49  --time_out_prep_mult                    0.1
% 7.01/1.49  --splitting_mode                        input
% 7.01/1.49  --splitting_grd                         true
% 7.01/1.49  --splitting_cvd                         false
% 7.01/1.49  --splitting_cvd_svl                     false
% 7.01/1.49  --splitting_nvd                         32
% 7.01/1.49  --sub_typing                            true
% 7.01/1.49  --prep_gs_sim                           true
% 7.01/1.49  --prep_unflatten                        true
% 7.01/1.49  --prep_res_sim                          true
% 7.01/1.49  --prep_upred                            true
% 7.01/1.49  --prep_sem_filter                       exhaustive
% 7.01/1.49  --prep_sem_filter_out                   false
% 7.01/1.49  --pred_elim                             true
% 7.01/1.49  --res_sim_input                         true
% 7.01/1.49  --eq_ax_congr_red                       true
% 7.01/1.49  --pure_diseq_elim                       true
% 7.01/1.49  --brand_transform                       false
% 7.01/1.49  --non_eq_to_eq                          false
% 7.01/1.49  --prep_def_merge                        true
% 7.01/1.49  --prep_def_merge_prop_impl              false
% 7.01/1.49  --prep_def_merge_mbd                    true
% 7.01/1.49  --prep_def_merge_tr_red                 false
% 7.01/1.49  --prep_def_merge_tr_cl                  false
% 7.01/1.49  --smt_preprocessing                     true
% 7.01/1.49  --smt_ac_axioms                         fast
% 7.01/1.49  --preprocessed_out                      false
% 7.01/1.49  --preprocessed_stats                    false
% 7.01/1.49  
% 7.01/1.49  ------ Abstraction refinement Options
% 7.01/1.49  
% 7.01/1.49  --abstr_ref                             []
% 7.01/1.49  --abstr_ref_prep                        false
% 7.01/1.49  --abstr_ref_until_sat                   false
% 7.01/1.49  --abstr_ref_sig_restrict                funpre
% 7.01/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.01/1.49  --abstr_ref_under                       []
% 7.01/1.49  
% 7.01/1.49  ------ SAT Options
% 7.01/1.49  
% 7.01/1.49  --sat_mode                              false
% 7.01/1.49  --sat_fm_restart_options                ""
% 7.01/1.49  --sat_gr_def                            false
% 7.01/1.49  --sat_epr_types                         true
% 7.01/1.49  --sat_non_cyclic_types                  false
% 7.01/1.49  --sat_finite_models                     false
% 7.01/1.49  --sat_fm_lemmas                         false
% 7.01/1.49  --sat_fm_prep                           false
% 7.01/1.49  --sat_fm_uc_incr                        true
% 7.01/1.49  --sat_out_model                         small
% 7.01/1.49  --sat_out_clauses                       false
% 7.01/1.49  
% 7.01/1.49  ------ QBF Options
% 7.01/1.49  
% 7.01/1.49  --qbf_mode                              false
% 7.01/1.49  --qbf_elim_univ                         false
% 7.01/1.49  --qbf_dom_inst                          none
% 7.01/1.49  --qbf_dom_pre_inst                      false
% 7.01/1.49  --qbf_sk_in                             false
% 7.01/1.49  --qbf_pred_elim                         true
% 7.01/1.49  --qbf_split                             512
% 7.01/1.49  
% 7.01/1.49  ------ BMC1 Options
% 7.01/1.49  
% 7.01/1.49  --bmc1_incremental                      false
% 7.01/1.49  --bmc1_axioms                           reachable_all
% 7.01/1.49  --bmc1_min_bound                        0
% 7.01/1.49  --bmc1_max_bound                        -1
% 7.01/1.49  --bmc1_max_bound_default                -1
% 7.01/1.49  --bmc1_symbol_reachability              true
% 7.01/1.49  --bmc1_property_lemmas                  false
% 7.01/1.49  --bmc1_k_induction                      false
% 7.01/1.49  --bmc1_non_equiv_states                 false
% 7.01/1.49  --bmc1_deadlock                         false
% 7.01/1.49  --bmc1_ucm                              false
% 7.01/1.49  --bmc1_add_unsat_core                   none
% 7.01/1.49  --bmc1_unsat_core_children              false
% 7.01/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.01/1.49  --bmc1_out_stat                         full
% 7.01/1.49  --bmc1_ground_init                      false
% 7.01/1.49  --bmc1_pre_inst_next_state              false
% 7.01/1.49  --bmc1_pre_inst_state                   false
% 7.01/1.49  --bmc1_pre_inst_reach_state             false
% 7.01/1.49  --bmc1_out_unsat_core                   false
% 7.01/1.49  --bmc1_aig_witness_out                  false
% 7.01/1.49  --bmc1_verbose                          false
% 7.01/1.49  --bmc1_dump_clauses_tptp                false
% 7.01/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.01/1.49  --bmc1_dump_file                        -
% 7.01/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.01/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.01/1.49  --bmc1_ucm_extend_mode                  1
% 7.01/1.49  --bmc1_ucm_init_mode                    2
% 7.01/1.49  --bmc1_ucm_cone_mode                    none
% 7.01/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.01/1.49  --bmc1_ucm_relax_model                  4
% 7.01/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.01/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.01/1.49  --bmc1_ucm_layered_model                none
% 7.01/1.49  --bmc1_ucm_max_lemma_size               10
% 7.01/1.49  
% 7.01/1.49  ------ AIG Options
% 7.01/1.49  
% 7.01/1.49  --aig_mode                              false
% 7.01/1.49  
% 7.01/1.49  ------ Instantiation Options
% 7.01/1.49  
% 7.01/1.49  --instantiation_flag                    true
% 7.01/1.49  --inst_sos_flag                         false
% 7.01/1.49  --inst_sos_phase                        true
% 7.01/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.01/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.01/1.49  --inst_lit_sel_side                     num_symb
% 7.01/1.49  --inst_solver_per_active                1400
% 7.01/1.49  --inst_solver_calls_frac                1.
% 7.01/1.49  --inst_passive_queue_type               priority_queues
% 7.01/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.01/1.49  --inst_passive_queues_freq              [25;2]
% 7.01/1.49  --inst_dismatching                      true
% 7.01/1.49  --inst_eager_unprocessed_to_passive     true
% 7.01/1.49  --inst_prop_sim_given                   true
% 7.01/1.49  --inst_prop_sim_new                     false
% 7.01/1.49  --inst_subs_new                         false
% 7.01/1.49  --inst_eq_res_simp                      false
% 7.01/1.49  --inst_subs_given                       false
% 7.01/1.49  --inst_orphan_elimination               true
% 7.01/1.49  --inst_learning_loop_flag               true
% 7.01/1.49  --inst_learning_start                   3000
% 7.01/1.49  --inst_learning_factor                  2
% 7.01/1.49  --inst_start_prop_sim_after_learn       3
% 7.01/1.49  --inst_sel_renew                        solver
% 7.01/1.49  --inst_lit_activity_flag                true
% 7.01/1.49  --inst_restr_to_given                   false
% 7.01/1.49  --inst_activity_threshold               500
% 7.01/1.49  --inst_out_proof                        true
% 7.01/1.49  
% 7.01/1.49  ------ Resolution Options
% 7.01/1.49  
% 7.01/1.49  --resolution_flag                       true
% 7.01/1.49  --res_lit_sel                           adaptive
% 7.01/1.49  --res_lit_sel_side                      none
% 7.01/1.49  --res_ordering                          kbo
% 7.01/1.49  --res_to_prop_solver                    active
% 7.01/1.49  --res_prop_simpl_new                    false
% 7.01/1.49  --res_prop_simpl_given                  true
% 7.01/1.49  --res_passive_queue_type                priority_queues
% 7.01/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.01/1.49  --res_passive_queues_freq               [15;5]
% 7.01/1.49  --res_forward_subs                      full
% 7.01/1.49  --res_backward_subs                     full
% 7.01/1.49  --res_forward_subs_resolution           true
% 7.01/1.49  --res_backward_subs_resolution          true
% 7.01/1.49  --res_orphan_elimination                true
% 7.01/1.49  --res_time_limit                        2.
% 7.01/1.49  --res_out_proof                         true
% 7.01/1.49  
% 7.01/1.49  ------ Superposition Options
% 7.01/1.49  
% 7.01/1.49  --superposition_flag                    true
% 7.01/1.49  --sup_passive_queue_type                priority_queues
% 7.01/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.01/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.01/1.49  --demod_completeness_check              fast
% 7.01/1.49  --demod_use_ground                      true
% 7.01/1.49  --sup_to_prop_solver                    passive
% 7.01/1.49  --sup_prop_simpl_new                    true
% 7.01/1.49  --sup_prop_simpl_given                  true
% 7.01/1.49  --sup_fun_splitting                     false
% 7.01/1.49  --sup_smt_interval                      50000
% 7.01/1.49  
% 7.01/1.49  ------ Superposition Simplification Setup
% 7.01/1.49  
% 7.01/1.49  --sup_indices_passive                   []
% 7.01/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.01/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.49  --sup_full_bw                           [BwDemod]
% 7.01/1.49  --sup_immed_triv                        [TrivRules]
% 7.01/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.01/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.49  --sup_immed_bw_main                     []
% 7.01/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.01/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.49  
% 7.01/1.49  ------ Combination Options
% 7.01/1.49  
% 7.01/1.49  --comb_res_mult                         3
% 7.01/1.49  --comb_sup_mult                         2
% 7.01/1.49  --comb_inst_mult                        10
% 7.01/1.49  
% 7.01/1.49  ------ Debug Options
% 7.01/1.49  
% 7.01/1.49  --dbg_backtrace                         false
% 7.01/1.49  --dbg_dump_prop_clauses                 false
% 7.01/1.49  --dbg_dump_prop_clauses_file            -
% 7.01/1.49  --dbg_out_stat                          false
% 7.01/1.49  ------ Parsing...
% 7.01/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.01/1.49  
% 7.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.01/1.49  
% 7.01/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.01/1.49  
% 7.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.01/1.49  ------ Proving...
% 7.01/1.49  ------ Problem Properties 
% 7.01/1.49  
% 7.01/1.49  
% 7.01/1.49  clauses                                 32
% 7.01/1.49  conjectures                             14
% 7.01/1.49  EPR                                     6
% 7.01/1.49  Horn                                    26
% 7.01/1.49  unary                                   11
% 7.01/1.49  binary                                  8
% 7.01/1.49  lits                                    82
% 7.01/1.49  lits eq                                 29
% 7.01/1.49  fd_pure                                 0
% 7.01/1.49  fd_pseudo                               0
% 7.01/1.49  fd_cond                                 3
% 7.01/1.49  fd_pseudo_cond                          2
% 7.01/1.49  AC symbols                              0
% 7.01/1.49  
% 7.01/1.49  ------ Schedule dynamic 5 is on 
% 7.01/1.49  
% 7.01/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.01/1.49  
% 7.01/1.49  
% 7.01/1.49  ------ 
% 7.01/1.49  Current options:
% 7.01/1.49  ------ 
% 7.01/1.49  
% 7.01/1.49  ------ Input Options
% 7.01/1.49  
% 7.01/1.49  --out_options                           all
% 7.01/1.49  --tptp_safe_out                         true
% 7.01/1.49  --problem_path                          ""
% 7.01/1.49  --include_path                          ""
% 7.01/1.49  --clausifier                            res/vclausify_rel
% 7.01/1.49  --clausifier_options                    --mode clausify
% 7.01/1.49  --stdin                                 false
% 7.01/1.49  --stats_out                             all
% 7.01/1.49  
% 7.01/1.49  ------ General Options
% 7.01/1.49  
% 7.01/1.49  --fof                                   false
% 7.01/1.49  --time_out_real                         305.
% 7.01/1.49  --time_out_virtual                      -1.
% 7.01/1.49  --symbol_type_check                     false
% 7.01/1.49  --clausify_out                          false
% 7.01/1.49  --sig_cnt_out                           false
% 7.01/1.49  --trig_cnt_out                          false
% 7.01/1.49  --trig_cnt_out_tolerance                1.
% 7.01/1.49  --trig_cnt_out_sk_spl                   false
% 7.01/1.49  --abstr_cl_out                          false
% 7.01/1.49  
% 7.01/1.49  ------ Global Options
% 7.01/1.49  
% 7.01/1.49  --schedule                              default
% 7.01/1.49  --add_important_lit                     false
% 7.01/1.49  --prop_solver_per_cl                    1000
% 7.01/1.49  --min_unsat_core                        false
% 7.01/1.49  --soft_assumptions                      false
% 7.01/1.49  --soft_lemma_size                       3
% 7.01/1.49  --prop_impl_unit_size                   0
% 7.01/1.49  --prop_impl_unit                        []
% 7.01/1.49  --share_sel_clauses                     true
% 7.01/1.49  --reset_solvers                         false
% 7.01/1.49  --bc_imp_inh                            [conj_cone]
% 7.01/1.49  --conj_cone_tolerance                   3.
% 7.01/1.49  --extra_neg_conj                        none
% 7.01/1.49  --large_theory_mode                     true
% 7.01/1.49  --prolific_symb_bound                   200
% 7.01/1.49  --lt_threshold                          2000
% 7.01/1.49  --clause_weak_htbl                      true
% 7.01/1.49  --gc_record_bc_elim                     false
% 7.01/1.49  
% 7.01/1.49  ------ Preprocessing Options
% 7.01/1.49  
% 7.01/1.49  --preprocessing_flag                    true
% 7.01/1.49  --time_out_prep_mult                    0.1
% 7.01/1.49  --splitting_mode                        input
% 7.01/1.49  --splitting_grd                         true
% 7.01/1.49  --splitting_cvd                         false
% 7.01/1.49  --splitting_cvd_svl                     false
% 7.01/1.49  --splitting_nvd                         32
% 7.01/1.49  --sub_typing                            true
% 7.01/1.49  --prep_gs_sim                           true
% 7.01/1.49  --prep_unflatten                        true
% 7.01/1.49  --prep_res_sim                          true
% 7.01/1.49  --prep_upred                            true
% 7.01/1.49  --prep_sem_filter                       exhaustive
% 7.01/1.49  --prep_sem_filter_out                   false
% 7.01/1.49  --pred_elim                             true
% 7.01/1.49  --res_sim_input                         true
% 7.01/1.49  --eq_ax_congr_red                       true
% 7.01/1.49  --pure_diseq_elim                       true
% 7.01/1.49  --brand_transform                       false
% 7.01/1.49  --non_eq_to_eq                          false
% 7.01/1.49  --prep_def_merge                        true
% 7.01/1.49  --prep_def_merge_prop_impl              false
% 7.01/1.49  --prep_def_merge_mbd                    true
% 7.01/1.49  --prep_def_merge_tr_red                 false
% 7.01/1.49  --prep_def_merge_tr_cl                  false
% 7.01/1.49  --smt_preprocessing                     true
% 7.01/1.49  --smt_ac_axioms                         fast
% 7.01/1.49  --preprocessed_out                      false
% 7.01/1.49  --preprocessed_stats                    false
% 7.01/1.49  
% 7.01/1.49  ------ Abstraction refinement Options
% 7.01/1.49  
% 7.01/1.49  --abstr_ref                             []
% 7.01/1.49  --abstr_ref_prep                        false
% 7.01/1.49  --abstr_ref_until_sat                   false
% 7.01/1.49  --abstr_ref_sig_restrict                funpre
% 7.01/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.01/1.49  --abstr_ref_under                       []
% 7.01/1.49  
% 7.01/1.49  ------ SAT Options
% 7.01/1.49  
% 7.01/1.49  --sat_mode                              false
% 7.01/1.49  --sat_fm_restart_options                ""
% 7.01/1.49  --sat_gr_def                            false
% 7.01/1.49  --sat_epr_types                         true
% 7.01/1.49  --sat_non_cyclic_types                  false
% 7.01/1.49  --sat_finite_models                     false
% 7.01/1.49  --sat_fm_lemmas                         false
% 7.01/1.49  --sat_fm_prep                           false
% 7.01/1.49  --sat_fm_uc_incr                        true
% 7.01/1.49  --sat_out_model                         small
% 7.01/1.49  --sat_out_clauses                       false
% 7.01/1.49  
% 7.01/1.49  ------ QBF Options
% 7.01/1.49  
% 7.01/1.49  --qbf_mode                              false
% 7.01/1.49  --qbf_elim_univ                         false
% 7.01/1.49  --qbf_dom_inst                          none
% 7.01/1.49  --qbf_dom_pre_inst                      false
% 7.01/1.49  --qbf_sk_in                             false
% 7.01/1.49  --qbf_pred_elim                         true
% 7.01/1.49  --qbf_split                             512
% 7.01/1.49  
% 7.01/1.49  ------ BMC1 Options
% 7.01/1.49  
% 7.01/1.49  --bmc1_incremental                      false
% 7.01/1.49  --bmc1_axioms                           reachable_all
% 7.01/1.49  --bmc1_min_bound                        0
% 7.01/1.49  --bmc1_max_bound                        -1
% 7.01/1.49  --bmc1_max_bound_default                -1
% 7.01/1.49  --bmc1_symbol_reachability              true
% 7.01/1.49  --bmc1_property_lemmas                  false
% 7.01/1.49  --bmc1_k_induction                      false
% 7.01/1.49  --bmc1_non_equiv_states                 false
% 7.01/1.49  --bmc1_deadlock                         false
% 7.01/1.49  --bmc1_ucm                              false
% 7.01/1.49  --bmc1_add_unsat_core                   none
% 7.01/1.49  --bmc1_unsat_core_children              false
% 7.01/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.01/1.49  --bmc1_out_stat                         full
% 7.01/1.49  --bmc1_ground_init                      false
% 7.01/1.49  --bmc1_pre_inst_next_state              false
% 7.01/1.49  --bmc1_pre_inst_state                   false
% 7.01/1.49  --bmc1_pre_inst_reach_state             false
% 7.01/1.49  --bmc1_out_unsat_core                   false
% 7.01/1.49  --bmc1_aig_witness_out                  false
% 7.01/1.49  --bmc1_verbose                          false
% 7.01/1.49  --bmc1_dump_clauses_tptp                false
% 7.01/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.01/1.49  --bmc1_dump_file                        -
% 7.01/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.01/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.01/1.49  --bmc1_ucm_extend_mode                  1
% 7.01/1.49  --bmc1_ucm_init_mode                    2
% 7.01/1.49  --bmc1_ucm_cone_mode                    none
% 7.01/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.01/1.49  --bmc1_ucm_relax_model                  4
% 7.01/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.01/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.01/1.49  --bmc1_ucm_layered_model                none
% 7.01/1.49  --bmc1_ucm_max_lemma_size               10
% 7.01/1.49  
% 7.01/1.49  ------ AIG Options
% 7.01/1.49  
% 7.01/1.49  --aig_mode                              false
% 7.01/1.49  
% 7.01/1.49  ------ Instantiation Options
% 7.01/1.49  
% 7.01/1.49  --instantiation_flag                    true
% 7.01/1.49  --inst_sos_flag                         false
% 7.01/1.49  --inst_sos_phase                        true
% 7.01/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.01/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.01/1.49  --inst_lit_sel_side                     none
% 7.01/1.49  --inst_solver_per_active                1400
% 7.01/1.49  --inst_solver_calls_frac                1.
% 7.01/1.49  --inst_passive_queue_type               priority_queues
% 7.01/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.01/1.49  --inst_passive_queues_freq              [25;2]
% 7.01/1.49  --inst_dismatching                      true
% 7.01/1.49  --inst_eager_unprocessed_to_passive     true
% 7.01/1.49  --inst_prop_sim_given                   true
% 7.01/1.49  --inst_prop_sim_new                     false
% 7.01/1.49  --inst_subs_new                         false
% 7.01/1.49  --inst_eq_res_simp                      false
% 7.01/1.49  --inst_subs_given                       false
% 7.01/1.49  --inst_orphan_elimination               true
% 7.01/1.49  --inst_learning_loop_flag               true
% 7.01/1.49  --inst_learning_start                   3000
% 7.01/1.49  --inst_learning_factor                  2
% 7.01/1.49  --inst_start_prop_sim_after_learn       3
% 7.01/1.49  --inst_sel_renew                        solver
% 7.01/1.49  --inst_lit_activity_flag                true
% 7.01/1.49  --inst_restr_to_given                   false
% 7.01/1.49  --inst_activity_threshold               500
% 7.01/1.49  --inst_out_proof                        true
% 7.01/1.49  
% 7.01/1.49  ------ Resolution Options
% 7.01/1.49  
% 7.01/1.49  --resolution_flag                       false
% 7.01/1.49  --res_lit_sel                           adaptive
% 7.01/1.49  --res_lit_sel_side                      none
% 7.01/1.49  --res_ordering                          kbo
% 7.01/1.49  --res_to_prop_solver                    active
% 7.01/1.49  --res_prop_simpl_new                    false
% 7.01/1.49  --res_prop_simpl_given                  true
% 7.01/1.49  --res_passive_queue_type                priority_queues
% 7.01/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.01/1.49  --res_passive_queues_freq               [15;5]
% 7.01/1.49  --res_forward_subs                      full
% 7.01/1.49  --res_backward_subs                     full
% 7.01/1.49  --res_forward_subs_resolution           true
% 7.01/1.49  --res_backward_subs_resolution          true
% 7.01/1.49  --res_orphan_elimination                true
% 7.01/1.49  --res_time_limit                        2.
% 7.01/1.49  --res_out_proof                         true
% 7.01/1.49  
% 7.01/1.49  ------ Superposition Options
% 7.01/1.49  
% 7.01/1.49  --superposition_flag                    true
% 7.01/1.49  --sup_passive_queue_type                priority_queues
% 7.01/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.01/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.01/1.49  --demod_completeness_check              fast
% 7.01/1.49  --demod_use_ground                      true
% 7.01/1.49  --sup_to_prop_solver                    passive
% 7.01/1.49  --sup_prop_simpl_new                    true
% 7.01/1.49  --sup_prop_simpl_given                  true
% 7.01/1.49  --sup_fun_splitting                     false
% 7.01/1.49  --sup_smt_interval                      50000
% 7.01/1.49  
% 7.01/1.49  ------ Superposition Simplification Setup
% 7.01/1.49  
% 7.01/1.49  --sup_indices_passive                   []
% 7.01/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.01/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.49  --sup_full_bw                           [BwDemod]
% 7.01/1.49  --sup_immed_triv                        [TrivRules]
% 7.01/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.01/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.49  --sup_immed_bw_main                     []
% 7.01/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.01/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.49  
% 7.01/1.49  ------ Combination Options
% 7.01/1.49  
% 7.01/1.49  --comb_res_mult                         3
% 7.01/1.49  --comb_sup_mult                         2
% 7.01/1.49  --comb_inst_mult                        10
% 7.01/1.49  
% 7.01/1.49  ------ Debug Options
% 7.01/1.49  
% 7.01/1.49  --dbg_backtrace                         false
% 7.01/1.49  --dbg_dump_prop_clauses                 false
% 7.01/1.49  --dbg_dump_prop_clauses_file            -
% 7.01/1.49  --dbg_out_stat                          false
% 7.01/1.49  
% 7.01/1.49  
% 7.01/1.49  
% 7.01/1.49  
% 7.01/1.49  ------ Proving...
% 7.01/1.49  
% 7.01/1.49  
% 7.01/1.49  % SZS status Theorem for theBenchmark.p
% 7.01/1.49  
% 7.01/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.01/1.49  
% 7.01/1.49  fof(f10,conjecture,(
% 7.01/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f11,negated_conjecture,(
% 7.01/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.01/1.49    inference(negated_conjecture,[],[f10])).
% 7.01/1.49  
% 7.01/1.49  fof(f25,plain,(
% 7.01/1.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | (k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0))) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | (k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.01/1.49    inference(ennf_transformation,[],[f11])).
% 7.01/1.49  
% 7.01/1.49  fof(f26,plain,(
% 7.01/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.01/1.49    inference(flattening,[],[f25])).
% 7.01/1.49  
% 7.01/1.49  fof(f31,plain,(
% 7.01/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK4 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5,X4] : (((k1_funct_1(sK4,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 7.01/1.49    introduced(choice_axiom,[])).
% 7.01/1.49  
% 7.01/1.49  fof(f30,plain,(
% 7.01/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK2)) | k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK1)) & ((k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK1)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK2))) & v2_funct_1(sK3) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.01/1.49    introduced(choice_axiom,[])).
% 7.01/1.49  
% 7.01/1.49  fof(f32,plain,(
% 7.01/1.49    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X4,X5] : (((k1_funct_1(sK4,X4) = X5 & r2_hidden(X4,sK2)) | k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK1)) & ((k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK1)) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2))) & v2_funct_1(sK3) & k2_relset_1(sK1,sK2,sK3) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f31,f30])).
% 7.01/1.49  
% 7.01/1.49  fof(f56,plain,(
% 7.01/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f7,axiom,(
% 7.01/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f19,plain,(
% 7.01/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.49    inference(ennf_transformation,[],[f7])).
% 7.01/1.49  
% 7.01/1.49  fof(f20,plain,(
% 7.01/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.49    inference(flattening,[],[f19])).
% 7.01/1.49  
% 7.01/1.49  fof(f29,plain,(
% 7.01/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.49    inference(nnf_transformation,[],[f20])).
% 7.01/1.49  
% 7.01/1.49  fof(f41,plain,(
% 7.01/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.01/1.49    inference(cnf_transformation,[],[f29])).
% 7.01/1.49  
% 7.01/1.49  fof(f5,axiom,(
% 7.01/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f17,plain,(
% 7.01/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.49    inference(ennf_transformation,[],[f5])).
% 7.01/1.49  
% 7.01/1.49  fof(f39,plain,(
% 7.01/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.01/1.49    inference(cnf_transformation,[],[f17])).
% 7.01/1.49  
% 7.01/1.49  fof(f55,plain,(
% 7.01/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f63,plain,(
% 7.01/1.49    k1_xboole_0 != sK1),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f53,plain,(
% 7.01/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f6,axiom,(
% 7.01/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f18,plain,(
% 7.01/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.01/1.49    inference(ennf_transformation,[],[f6])).
% 7.01/1.49  
% 7.01/1.49  fof(f40,plain,(
% 7.01/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.01/1.49    inference(cnf_transformation,[],[f18])).
% 7.01/1.49  
% 7.01/1.49  fof(f57,plain,(
% 7.01/1.49    k2_relset_1(sK1,sK2,sK3) = sK2),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f3,axiom,(
% 7.01/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f13,plain,(
% 7.01/1.49    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.01/1.49    inference(ennf_transformation,[],[f3])).
% 7.01/1.49  
% 7.01/1.49  fof(f14,plain,(
% 7.01/1.49    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.01/1.49    inference(flattening,[],[f13])).
% 7.01/1.49  
% 7.01/1.49  fof(f35,plain,(
% 7.01/1.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f14])).
% 7.01/1.49  
% 7.01/1.49  fof(f58,plain,(
% 7.01/1.49    v2_funct_1(sK3)),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f51,plain,(
% 7.01/1.49    v1_funct_1(sK3)),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f1,axiom,(
% 7.01/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f12,plain,(
% 7.01/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.01/1.49    inference(ennf_transformation,[],[f1])).
% 7.01/1.49  
% 7.01/1.49  fof(f33,plain,(
% 7.01/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f12])).
% 7.01/1.49  
% 7.01/1.49  fof(f2,axiom,(
% 7.01/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f34,plain,(
% 7.01/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.01/1.49    inference(cnf_transformation,[],[f2])).
% 7.01/1.49  
% 7.01/1.49  fof(f4,axiom,(
% 7.01/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f15,plain,(
% 7.01/1.49    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.01/1.49    inference(ennf_transformation,[],[f4])).
% 7.01/1.49  
% 7.01/1.49  fof(f16,plain,(
% 7.01/1.49    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.01/1.49    inference(flattening,[],[f15])).
% 7.01/1.49  
% 7.01/1.49  fof(f27,plain,(
% 7.01/1.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 7.01/1.49    introduced(choice_axiom,[])).
% 7.01/1.49  
% 7.01/1.49  fof(f28,plain,(
% 7.01/1.49    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f27])).
% 7.01/1.49  
% 7.01/1.49  fof(f37,plain,(
% 7.01/1.49    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f28])).
% 7.01/1.49  
% 7.01/1.49  fof(f52,plain,(
% 7.01/1.49    v1_funct_2(sK3,sK1,sK2)),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f8,axiom,(
% 7.01/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f21,plain,(
% 7.01/1.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.01/1.49    inference(ennf_transformation,[],[f8])).
% 7.01/1.49  
% 7.01/1.49  fof(f22,plain,(
% 7.01/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.01/1.49    inference(flattening,[],[f21])).
% 7.01/1.49  
% 7.01/1.49  fof(f47,plain,(
% 7.01/1.49    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f22])).
% 7.01/1.49  
% 7.01/1.49  fof(f49,plain,(
% 7.01/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f22])).
% 7.01/1.49  
% 7.01/1.49  fof(f54,plain,(
% 7.01/1.49    v1_funct_1(sK4)),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f65,plain,(
% 7.01/1.49    k2_funct_1(sK3) != sK4),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f59,plain,(
% 7.01/1.49    ( ! [X4,X5] : (r2_hidden(X5,sK1) | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f74,plain,(
% 7.01/1.49    ( ! [X4] : (r2_hidden(k1_funct_1(sK4,X4),sK1) | ~r2_hidden(X4,sK2)) )),
% 7.01/1.49    inference(equality_resolution,[],[f59])).
% 7.01/1.49  
% 7.01/1.49  fof(f9,axiom,(
% 7.01/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 7.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.49  
% 7.01/1.49  fof(f23,plain,(
% 7.01/1.49    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.01/1.49    inference(ennf_transformation,[],[f9])).
% 7.01/1.49  
% 7.01/1.49  fof(f24,plain,(
% 7.01/1.49    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.01/1.49    inference(flattening,[],[f23])).
% 7.01/1.49  
% 7.01/1.49  fof(f50,plain,(
% 7.01/1.49    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f24])).
% 7.01/1.49  
% 7.01/1.49  fof(f64,plain,(
% 7.01/1.49    k1_xboole_0 != sK2),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f60,plain,(
% 7.01/1.49    ( ! [X4,X5] : (k1_funct_1(sK3,X5) = X4 | k1_funct_1(sK4,X4) != X5 | ~r2_hidden(X4,sK2)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f32])).
% 7.01/1.49  
% 7.01/1.49  fof(f73,plain,(
% 7.01/1.49    ( ! [X4] : (k1_funct_1(sK3,k1_funct_1(sK4,X4)) = X4 | ~r2_hidden(X4,sK2)) )),
% 7.01/1.49    inference(equality_resolution,[],[f60])).
% 7.01/1.49  
% 7.01/1.49  fof(f38,plain,(
% 7.01/1.49    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.01/1.49    inference(cnf_transformation,[],[f28])).
% 7.01/1.49  
% 7.01/1.49  cnf(c_27,negated_conjecture,
% 7.01/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.01/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1191,plain,
% 7.01/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_13,plain,
% 7.01/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.01/1.49      | k1_xboole_0 = X2 ),
% 7.01/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1196,plain,
% 7.01/1.49      ( k1_relset_1(X0,X1,X2) = X0
% 7.01/1.49      | k1_xboole_0 = X1
% 7.01/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.01/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_3445,plain,
% 7.01/1.49      ( k1_relset_1(sK2,sK1,sK4) = sK2
% 7.01/1.49      | sK1 = k1_xboole_0
% 7.01/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_1191,c_1196]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_6,plain,
% 7.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.01/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1203,plain,
% 7.01/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.01/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2194,plain,
% 7.01/1.49      ( k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_1191,c_1203]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_3458,plain,
% 7.01/1.49      ( k1_relat_1(sK4) = sK2
% 7.01/1.49      | sK1 = k1_xboole_0
% 7.01/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top ),
% 7.01/1.49      inference(demodulation,[status(thm)],[c_3445,c_2194]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_28,negated_conjecture,
% 7.01/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.01/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_37,plain,
% 7.01/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_20,negated_conjecture,
% 7.01/1.49      ( k1_xboole_0 != sK1 ),
% 7.01/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_677,plain,( X0 = X0 ),theory(equality) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_706,plain,
% 7.01/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_677]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_678,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1496,plain,
% 7.01/1.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_678]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1497,plain,
% 7.01/1.49      ( sK1 != k1_xboole_0
% 7.01/1.49      | k1_xboole_0 = sK1
% 7.01/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_1496]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_6251,plain,
% 7.01/1.49      ( k1_relat_1(sK4) = sK2 ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_3458,c_37,c_20,c_706,c_1497]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_30,negated_conjecture,
% 7.01/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.01/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1188,plain,
% 7.01/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_7,plain,
% 7.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.01/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1202,plain,
% 7.01/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.01/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2106,plain,
% 7.01/1.49      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_1188,c_1202]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_26,negated_conjecture,
% 7.01/1.49      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 7.01/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2108,plain,
% 7.01/1.49      ( k2_relat_1(sK3) = sK2 ),
% 7.01/1.49      inference(light_normalisation,[status(thm)],[c_2106,c_26]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_3,plain,
% 7.01/1.49      ( ~ v1_funct_1(X0)
% 7.01/1.49      | ~ v2_funct_1(X0)
% 7.01/1.49      | ~ v1_relat_1(X0)
% 7.01/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.01/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_25,negated_conjecture,
% 7.01/1.49      ( v2_funct_1(sK3) ),
% 7.01/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_429,plain,
% 7.01/1.49      ( ~ v1_funct_1(X0)
% 7.01/1.49      | ~ v1_relat_1(X0)
% 7.01/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.01/1.49      | sK3 != X0 ),
% 7.01/1.49      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_430,plain,
% 7.01/1.49      ( ~ v1_funct_1(sK3)
% 7.01/1.49      | ~ v1_relat_1(sK3)
% 7.01/1.49      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 7.01/1.49      inference(unflattening,[status(thm)],[c_429]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_32,negated_conjecture,
% 7.01/1.49      ( v1_funct_1(sK3) ),
% 7.01/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_432,plain,
% 7.01/1.49      ( ~ v1_relat_1(sK3)
% 7.01/1.49      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_430,c_32]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1181,plain,
% 7.01/1.49      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 7.01/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2113,plain,
% 7.01/1.49      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 7.01/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.01/1.49      inference(demodulation,[status(thm)],[c_2108,c_1181]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_35,plain,
% 7.01/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_0,plain,
% 7.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.01/1.49      | ~ v1_relat_1(X1)
% 7.01/1.49      | v1_relat_1(X0) ),
% 7.01/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1462,plain,
% 7.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | v1_relat_1(X0)
% 7.01/1.49      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1833,plain,
% 7.01/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.01/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 7.01/1.49      | v1_relat_1(sK3) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_1462]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1834,plain,
% 7.01/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.01/1.49      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 7.01/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1,plain,
% 7.01/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.01/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2078,plain,
% 7.01/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2079,plain,
% 7.01/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_2078]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2656,plain,
% 7.01/1.49      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_2113,c_35,c_1834,c_2079]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_5,plain,
% 7.01/1.49      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 7.01/1.49      | ~ v1_funct_1(X0)
% 7.01/1.49      | ~ v1_funct_1(X1)
% 7.01/1.49      | ~ v1_relat_1(X0)
% 7.01/1.49      | ~ v1_relat_1(X1)
% 7.01/1.49      | X0 = X1
% 7.01/1.49      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.01/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1204,plain,
% 7.01/1.49      ( X0 = X1
% 7.01/1.49      | k1_relat_1(X1) != k1_relat_1(X0)
% 7.01/1.49      | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) = iProver_top
% 7.01/1.49      | v1_funct_1(X0) != iProver_top
% 7.01/1.49      | v1_funct_1(X1) != iProver_top
% 7.01/1.49      | v1_relat_1(X0) != iProver_top
% 7.01/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_3575,plain,
% 7.01/1.49      ( k1_relat_1(X0) != sK2
% 7.01/1.49      | k2_funct_1(sK3) = X0
% 7.01/1.49      | r2_hidden(sK0(X0,k2_funct_1(sK3)),k1_relat_1(X0)) = iProver_top
% 7.01/1.49      | v1_funct_1(X0) != iProver_top
% 7.01/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.01/1.49      | v1_relat_1(X0) != iProver_top
% 7.01/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_2656,c_1204]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_31,negated_conjecture,
% 7.01/1.49      ( v1_funct_2(sK3,sK1,sK2) ),
% 7.01/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_34,plain,
% 7.01/1.49      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_16,plain,
% 7.01/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | ~ v1_funct_1(X0)
% 7.01/1.49      | v1_funct_1(k2_funct_1(X0))
% 7.01/1.49      | ~ v2_funct_1(X0)
% 7.01/1.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.01/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_357,plain,
% 7.01/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | ~ v1_funct_1(X0)
% 7.01/1.49      | v1_funct_1(k2_funct_1(X0))
% 7.01/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.01/1.49      | sK3 != X0 ),
% 7.01/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_358,plain,
% 7.01/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | v1_funct_1(k2_funct_1(sK3))
% 7.01/1.49      | ~ v1_funct_1(sK3)
% 7.01/1.49      | k2_relset_1(X0,X1,sK3) != X1 ),
% 7.01/1.49      inference(unflattening,[status(thm)],[c_357]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_362,plain,
% 7.01/1.49      ( v1_funct_1(k2_funct_1(sK3))
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | k2_relset_1(X0,X1,sK3) != X1 ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_358,c_32]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_363,plain,
% 7.01/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | v1_funct_1(k2_funct_1(sK3))
% 7.01/1.49      | k2_relset_1(X0,X1,sK3) != X1 ),
% 7.01/1.49      inference(renaming,[status(thm)],[c_362]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1435,plain,
% 7.01/1.49      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.01/1.49      | v1_funct_1(k2_funct_1(sK3))
% 7.01/1.49      | k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_363]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1436,plain,
% 7.01/1.49      ( k2_relset_1(sK1,sK2,sK3) != sK2
% 7.01/1.49      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.01/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.01/1.49      | v1_funct_1(k2_funct_1(sK3)) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1435]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_14,plain,
% 7.01/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.01/1.49      | ~ v1_funct_1(X0)
% 7.01/1.49      | ~ v2_funct_1(X0)
% 7.01/1.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.01/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_405,plain,
% 7.01/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.01/1.49      | ~ v1_funct_1(X0)
% 7.01/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.01/1.49      | sK3 != X0 ),
% 7.01/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_406,plain,
% 7.01/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | ~ v1_funct_1(sK3)
% 7.01/1.49      | k2_relset_1(X0,X1,sK3) != X1 ),
% 7.01/1.49      inference(unflattening,[status(thm)],[c_405]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_410,plain,
% 7.01/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.01/1.49      | ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | k2_relset_1(X0,X1,sK3) != X1 ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_406,c_32]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_411,plain,
% 7.01/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | k2_relset_1(X0,X1,sK3) != X1 ),
% 7.01/1.49      inference(renaming,[status(thm)],[c_410]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1451,plain,
% 7.01/1.49      ( ~ v1_funct_2(sK3,sK1,sK2)
% 7.01/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.01/1.49      | k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_411]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1452,plain,
% 7.01/1.49      ( k2_relset_1(sK1,sK2,sK3) != sK2
% 7.01/1.49      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.01/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top
% 7.01/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1836,plain,
% 7.01/1.49      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.01/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 7.01/1.49      | v1_relat_1(k2_funct_1(sK3)) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_1462]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1837,plain,
% 7.01/1.49      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.01/1.49      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.01/1.49      | v1_relat_1(k2_funct_1(sK3)) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1836]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2075,plain,
% 7.01/1.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2076,plain,
% 7.01/1.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_2075]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_4420,plain,
% 7.01/1.49      ( v1_relat_1(X0) != iProver_top
% 7.01/1.49      | k1_relat_1(X0) != sK2
% 7.01/1.49      | k2_funct_1(sK3) = X0
% 7.01/1.49      | r2_hidden(sK0(X0,k2_funct_1(sK3)),k1_relat_1(X0)) = iProver_top
% 7.01/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_3575,c_34,c_35,c_26,c_1436,c_1452,c_1837,c_2076]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_4421,plain,
% 7.01/1.49      ( k1_relat_1(X0) != sK2
% 7.01/1.49      | k2_funct_1(sK3) = X0
% 7.01/1.49      | r2_hidden(sK0(X0,k2_funct_1(sK3)),k1_relat_1(X0)) = iProver_top
% 7.01/1.49      | v1_funct_1(X0) != iProver_top
% 7.01/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.01/1.49      inference(renaming,[status(thm)],[c_4420]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_6257,plain,
% 7.01/1.49      ( k2_funct_1(sK3) = sK4
% 7.01/1.49      | r2_hidden(sK0(sK4,k2_funct_1(sK3)),k1_relat_1(sK4)) = iProver_top
% 7.01/1.49      | v1_funct_1(sK4) != iProver_top
% 7.01/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_6251,c_4421]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_6278,plain,
% 7.01/1.49      ( k2_funct_1(sK3) = sK4
% 7.01/1.49      | r2_hidden(sK0(sK4,k2_funct_1(sK3)),sK2) = iProver_top
% 7.01/1.49      | v1_funct_1(sK4) != iProver_top
% 7.01/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.01/1.49      inference(light_normalisation,[status(thm)],[c_6257,c_6251]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_29,negated_conjecture,
% 7.01/1.49      ( v1_funct_1(sK4) ),
% 7.01/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_36,plain,
% 7.01/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_38,plain,
% 7.01/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_18,negated_conjecture,
% 7.01/1.49      ( k2_funct_1(sK3) != sK4 ),
% 7.01/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1830,plain,
% 7.01/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.01/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 7.01/1.49      | v1_relat_1(sK4) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_1462]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1831,plain,
% 7.01/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.01/1.49      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.01/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1830]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_16863,plain,
% 7.01/1.49      ( r2_hidden(sK0(sK4,k2_funct_1(sK3)),sK2) = iProver_top ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_6278,c_36,c_38,c_18,c_1831,c_2076]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_24,negated_conjecture,
% 7.01/1.49      ( ~ r2_hidden(X0,sK2) | r2_hidden(k1_funct_1(sK4,X0),sK1) ),
% 7.01/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1192,plain,
% 7.01/1.49      ( r2_hidden(X0,sK2) != iProver_top
% 7.01/1.49      | r2_hidden(k1_funct_1(sK4,X0),sK1) = iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_17,plain,
% 7.01/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.01/1.49      | ~ r2_hidden(X3,X1)
% 7.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | ~ v1_funct_1(X0)
% 7.01/1.49      | ~ v2_funct_1(X0)
% 7.01/1.49      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 7.01/1.49      | k1_xboole_0 = X2 ),
% 7.01/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_330,plain,
% 7.01/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.01/1.49      | ~ r2_hidden(X3,X1)
% 7.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.01/1.49      | ~ v1_funct_1(X0)
% 7.01/1.49      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 7.01/1.49      | sK3 != X0
% 7.01/1.49      | k1_xboole_0 = X2 ),
% 7.01/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_331,plain,
% 7.01/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | ~ r2_hidden(X2,X0)
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | ~ v1_funct_1(sK3)
% 7.01/1.49      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X2)) = X2
% 7.01/1.49      | k1_xboole_0 = X1 ),
% 7.01/1.49      inference(unflattening,[status(thm)],[c_330]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_335,plain,
% 7.01/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | ~ r2_hidden(X2,X0)
% 7.01/1.49      | ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X2)) = X2
% 7.01/1.49      | k1_xboole_0 = X1 ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_331,c_32]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_336,plain,
% 7.01/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 7.01/1.49      | ~ r2_hidden(X2,X0)
% 7.01/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.01/1.49      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X2)) = X2
% 7.01/1.49      | k1_xboole_0 = X1 ),
% 7.01/1.49      inference(renaming,[status(thm)],[c_335]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1185,plain,
% 7.01/1.49      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 7.01/1.49      | k1_xboole_0 = X1
% 7.01/1.49      | v1_funct_2(sK3,X2,X1) != iProver_top
% 7.01/1.49      | r2_hidden(X0,X2) != iProver_top
% 7.01/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_3404,plain,
% 7.01/1.49      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 7.01/1.49      | sK2 = k1_xboole_0
% 7.01/1.49      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 7.01/1.49      | r2_hidden(X0,sK1) != iProver_top ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_1188,c_1185]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_19,negated_conjecture,
% 7.01/1.49      ( k1_xboole_0 != sK2 ),
% 7.01/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1494,plain,
% 7.01/1.49      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_678]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1495,plain,
% 7.01/1.49      ( sK2 != k1_xboole_0
% 7.01/1.49      | k1_xboole_0 = sK2
% 7.01/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_1494]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_4052,plain,
% 7.01/1.49      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 7.01/1.49      | r2_hidden(X0,sK1) != iProver_top ),
% 7.01/1.49      inference(global_propositional_subsumption,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_3404,c_34,c_19,c_706,c_1495]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_4060,plain,
% 7.01/1.49      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,X0))) = k1_funct_1(sK4,X0)
% 7.01/1.49      | r2_hidden(X0,sK2) != iProver_top ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_1192,c_4052]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_16943,plain,
% 7.01/1.49      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3))))) = k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3))) ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_16863,c_4060]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_23,negated_conjecture,
% 7.01/1.49      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0 ),
% 7.01/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1193,plain,
% 7.01/1.49      ( k1_funct_1(sK3,k1_funct_1(sK4,X0)) = X0
% 7.01/1.49      | r2_hidden(X0,sK2) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_16952,plain,
% 7.01/1.49      ( k1_funct_1(sK3,k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3)))) = sK0(sK4,k2_funct_1(sK3)) ),
% 7.01/1.49      inference(superposition,[status(thm)],[c_16863,c_1193]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_16963,plain,
% 7.01/1.49      ( k1_funct_1(k2_funct_1(sK3),sK0(sK4,k2_funct_1(sK3))) = k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3))) ),
% 7.01/1.49      inference(light_normalisation,[status(thm)],[c_16943,c_16952]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_15044,plain,
% 7.01/1.49      ( sK0(k2_funct_1(sK3),sK4) = sK0(k2_funct_1(sK3),sK4) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_677]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_687,plain,
% 7.01/1.49      ( X0 != X1 | X2 != X3 | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
% 7.01/1.49      theory(equality) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_12732,plain,
% 7.01/1.49      ( k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) = k1_funct_1(k2_funct_1(sK3),sK0(k2_funct_1(sK3),sK4))
% 7.01/1.49      | sK0(k2_funct_1(sK3),sK4) != sK0(k2_funct_1(sK3),sK4)
% 7.01/1.49      | sK4 != k2_funct_1(sK3) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_687]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_3478,plain,
% 7.01/1.49      ( k1_relat_1(k2_funct_1(sK3)) != X0
% 7.01/1.49      | k1_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK4)
% 7.01/1.49      | k1_relat_1(sK4) != X0 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_678]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_7859,plain,
% 7.01/1.49      ( k1_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK4)
% 7.01/1.49      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 7.01/1.49      | k1_relat_1(sK4) != sK2 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_3478]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2301,plain,
% 7.01/1.49      ( k1_relat_1(k2_funct_1(sK3)) != X0
% 7.01/1.49      | k1_relat_1(sK4) != X0
% 7.01/1.49      | k1_relat_1(sK4) = k1_relat_1(k2_funct_1(sK3)) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_678]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_7861,plain,
% 7.01/1.49      ( k1_relat_1(k2_funct_1(sK3)) != sK2
% 7.01/1.49      | k1_relat_1(sK4) = k1_relat_1(k2_funct_1(sK3))
% 7.01/1.49      | k1_relat_1(sK4) != sK2 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_2301]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_4,plain,
% 7.01/1.49      ( ~ v1_funct_1(X0)
% 7.01/1.49      | ~ v1_funct_1(X1)
% 7.01/1.49      | ~ v1_relat_1(X0)
% 7.01/1.49      | ~ v1_relat_1(X1)
% 7.01/1.49      | X0 = X1
% 7.01/1.49      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 7.01/1.49      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 7.01/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1663,plain,
% 7.01/1.49      ( ~ v1_funct_1(X0)
% 7.01/1.49      | ~ v1_funct_1(sK4)
% 7.01/1.49      | ~ v1_relat_1(X0)
% 7.01/1.49      | ~ v1_relat_1(sK4)
% 7.01/1.49      | k1_funct_1(X0,sK0(sK4,X0)) != k1_funct_1(sK4,sK0(sK4,X0))
% 7.01/1.49      | k1_relat_1(X0) != k1_relat_1(sK4)
% 7.01/1.49      | sK4 = X0 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_2652,plain,
% 7.01/1.49      ( ~ v1_funct_1(k2_funct_1(sK3))
% 7.01/1.49      | ~ v1_funct_1(sK4)
% 7.01/1.49      | ~ v1_relat_1(k2_funct_1(sK3))
% 7.01/1.49      | ~ v1_relat_1(sK4)
% 7.01/1.49      | k1_funct_1(k2_funct_1(sK3),sK0(sK4,k2_funct_1(sK3))) != k1_funct_1(sK4,sK0(sK4,k2_funct_1(sK3)))
% 7.01/1.49      | k1_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK4)
% 7.01/1.49      | sK4 = k2_funct_1(sK3) ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_1663]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1559,plain,
% 7.01/1.49      ( ~ v1_funct_1(k2_funct_1(sK3))
% 7.01/1.49      | ~ v1_funct_1(sK4)
% 7.01/1.49      | ~ v1_relat_1(k2_funct_1(sK3))
% 7.01/1.49      | ~ v1_relat_1(sK4)
% 7.01/1.49      | k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) != k1_funct_1(k2_funct_1(sK3),sK0(k2_funct_1(sK3),sK4))
% 7.01/1.49      | k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
% 7.01/1.49      | k2_funct_1(sK3) = sK4 ),
% 7.01/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(c_1560,plain,
% 7.01/1.49      ( k1_funct_1(sK4,sK0(k2_funct_1(sK3),sK4)) != k1_funct_1(k2_funct_1(sK3),sK0(k2_funct_1(sK3),sK4))
% 7.01/1.49      | k1_relat_1(sK4) != k1_relat_1(k2_funct_1(sK3))
% 7.01/1.49      | k2_funct_1(sK3) = sK4
% 7.01/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.01/1.49      | v1_funct_1(sK4) != iProver_top
% 7.01/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 7.01/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 7.01/1.49  
% 7.01/1.49  cnf(contradiction,plain,
% 7.01/1.49      ( $false ),
% 7.01/1.49      inference(minisat,
% 7.01/1.49                [status(thm)],
% 7.01/1.49                [c_16963,c_15044,c_12732,c_7859,c_7861,c_3458,c_2652,
% 7.01/1.49                 c_2113,c_2079,c_2076,c_2075,c_1837,c_1836,c_1834,c_1831,
% 7.01/1.49                 c_1830,c_1560,c_1497,c_1452,c_1451,c_1436,c_1435,c_706,
% 7.01/1.49                 c_18,c_20,c_26,c_38,c_27,c_37,c_36,c_29,c_35,c_30,c_34,
% 7.01/1.49                 c_31]) ).
% 7.01/1.49  
% 7.01/1.49  
% 7.01/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.01/1.49  
% 7.01/1.49  ------                               Statistics
% 7.01/1.49  
% 7.01/1.49  ------ General
% 7.01/1.49  
% 7.01/1.49  abstr_ref_over_cycles:                  0
% 7.01/1.49  abstr_ref_under_cycles:                 0
% 7.01/1.49  gc_basic_clause_elim:                   0
% 7.01/1.49  forced_gc_time:                         0
% 7.01/1.49  parsing_time:                           0.026
% 7.01/1.49  unif_index_cands_time:                  0.
% 7.01/1.49  unif_index_add_time:                    0.
% 7.01/1.49  orderings_time:                         0.
% 7.01/1.49  out_proof_time:                         0.012
% 7.01/1.49  total_time:                             0.585
% 7.01/1.49  num_of_symbols:                         51
% 7.01/1.49  num_of_terms:                           12173
% 7.01/1.49  
% 7.01/1.49  ------ Preprocessing
% 7.01/1.49  
% 7.01/1.49  num_of_splits:                          0
% 7.01/1.49  num_of_split_atoms:                     0
% 7.01/1.49  num_of_reused_defs:                     0
% 7.01/1.49  num_eq_ax_congr_red:                    12
% 7.01/1.49  num_of_sem_filtered_clauses:            1
% 7.01/1.49  num_of_subtypes:                        0
% 7.01/1.49  monotx_restored_types:                  0
% 7.01/1.49  sat_num_of_epr_types:                   0
% 7.01/1.49  sat_num_of_non_cyclic_types:            0
% 7.01/1.49  sat_guarded_non_collapsed_types:        0
% 7.01/1.49  num_pure_diseq_elim:                    0
% 7.01/1.49  simp_replaced_by:                       0
% 7.01/1.49  res_preprocessed:                       160
% 7.01/1.49  prep_upred:                             0
% 7.01/1.49  prep_unflattend:                        6
% 7.01/1.49  smt_new_axioms:                         0
% 7.01/1.49  pred_elim_cands:                        5
% 7.01/1.49  pred_elim:                              1
% 7.01/1.49  pred_elim_cl:                           1
% 7.01/1.49  pred_elim_cycles:                       3
% 7.01/1.49  merged_defs:                            0
% 7.01/1.49  merged_defs_ncl:                        0
% 7.01/1.49  bin_hyper_res:                          0
% 7.01/1.49  prep_cycles:                            4
% 7.01/1.49  pred_elim_time:                         0.004
% 7.01/1.49  splitting_time:                         0.
% 7.01/1.49  sem_filter_time:                        0.
% 7.01/1.49  monotx_time:                            0.
% 7.01/1.49  subtype_inf_time:                       0.
% 7.01/1.49  
% 7.01/1.49  ------ Problem properties
% 7.01/1.49  
% 7.01/1.49  clauses:                                32
% 7.01/1.49  conjectures:                            14
% 7.01/1.49  epr:                                    6
% 7.01/1.49  horn:                                   26
% 7.01/1.49  ground:                                 12
% 7.01/1.49  unary:                                  11
% 7.01/1.49  binary:                                 8
% 7.01/1.49  lits:                                   82
% 7.01/1.49  lits_eq:                                29
% 7.01/1.49  fd_pure:                                0
% 7.01/1.49  fd_pseudo:                              0
% 7.01/1.49  fd_cond:                                3
% 7.01/1.49  fd_pseudo_cond:                         2
% 7.01/1.49  ac_symbols:                             0
% 7.01/1.49  
% 7.01/1.49  ------ Propositional Solver
% 7.01/1.49  
% 7.01/1.49  prop_solver_calls:                      34
% 7.01/1.49  prop_fast_solver_calls:                 1461
% 7.01/1.49  smt_solver_calls:                       0
% 7.01/1.49  smt_fast_solver_calls:                  0
% 7.01/1.49  prop_num_of_clauses:                    5546
% 7.01/1.49  prop_preprocess_simplified:             11828
% 7.01/1.49  prop_fo_subsumed:                       42
% 7.01/1.49  prop_solver_time:                       0.
% 7.01/1.49  smt_solver_time:                        0.
% 7.01/1.49  smt_fast_solver_time:                   0.
% 7.01/1.49  prop_fast_solver_time:                  0.
% 7.01/1.49  prop_unsat_core_time:                   0.
% 7.01/1.49  
% 7.01/1.49  ------ QBF
% 7.01/1.49  
% 7.01/1.49  qbf_q_res:                              0
% 7.01/1.49  qbf_num_tautologies:                    0
% 7.01/1.49  qbf_prep_cycles:                        0
% 7.01/1.49  
% 7.01/1.49  ------ BMC1
% 7.01/1.49  
% 7.01/1.49  bmc1_current_bound:                     -1
% 7.01/1.49  bmc1_last_solved_bound:                 -1
% 7.01/1.49  bmc1_unsat_core_size:                   -1
% 7.01/1.49  bmc1_unsat_core_parents_size:           -1
% 7.01/1.49  bmc1_merge_next_fun:                    0
% 7.01/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.01/1.49  
% 7.01/1.49  ------ Instantiation
% 7.01/1.49  
% 7.01/1.49  inst_num_of_clauses:                    2169
% 7.01/1.49  inst_num_in_passive:                    520
% 7.01/1.49  inst_num_in_active:                     1121
% 7.01/1.49  inst_num_in_unprocessed:                528
% 7.01/1.49  inst_num_of_loops:                      1150
% 7.01/1.49  inst_num_of_learning_restarts:          0
% 7.01/1.49  inst_num_moves_active_passive:          23
% 7.01/1.49  inst_lit_activity:                      0
% 7.01/1.49  inst_lit_activity_moves:                0
% 7.01/1.49  inst_num_tautologies:                   0
% 7.01/1.49  inst_num_prop_implied:                  0
% 7.01/1.49  inst_num_existing_simplified:           0
% 7.01/1.49  inst_num_eq_res_simplified:             0
% 7.01/1.49  inst_num_child_elim:                    0
% 7.01/1.49  inst_num_of_dismatching_blockings:      729
% 7.01/1.49  inst_num_of_non_proper_insts:           2567
% 7.01/1.49  inst_num_of_duplicates:                 0
% 7.01/1.49  inst_inst_num_from_inst_to_res:         0
% 7.01/1.49  inst_dismatching_checking_time:         0.
% 7.01/1.49  
% 7.01/1.49  ------ Resolution
% 7.01/1.49  
% 7.01/1.49  res_num_of_clauses:                     0
% 7.01/1.49  res_num_in_passive:                     0
% 7.01/1.49  res_num_in_active:                      0
% 7.01/1.49  res_num_of_loops:                       164
% 7.01/1.49  res_forward_subset_subsumed:            413
% 7.01/1.49  res_backward_subset_subsumed:           2
% 7.01/1.49  res_forward_subsumed:                   0
% 7.01/1.49  res_backward_subsumed:                  0
% 7.01/1.49  res_forward_subsumption_resolution:     0
% 7.01/1.49  res_backward_subsumption_resolution:    0
% 7.01/1.49  res_clause_to_clause_subsumption:       4867
% 7.01/1.49  res_orphan_elimination:                 0
% 7.01/1.49  res_tautology_del:                      132
% 7.01/1.49  res_num_eq_res_simplified:              0
% 7.01/1.49  res_num_sel_changes:                    0
% 7.01/1.49  res_moves_from_active_to_pass:          0
% 7.01/1.49  
% 7.01/1.49  ------ Superposition
% 7.01/1.49  
% 7.01/1.49  sup_time_total:                         0.
% 7.01/1.49  sup_time_generating:                    0.
% 7.01/1.49  sup_time_sim_full:                      0.
% 7.01/1.49  sup_time_sim_immed:                     0.
% 7.01/1.49  
% 7.01/1.49  sup_num_of_clauses:                     235
% 7.01/1.49  sup_num_in_active:                      222
% 7.01/1.49  sup_num_in_passive:                     13
% 7.01/1.49  sup_num_of_loops:                       228
% 7.01/1.49  sup_fw_superposition:                   200
% 7.01/1.49  sup_bw_superposition:                   100
% 7.01/1.49  sup_immediate_simplified:               103
% 7.01/1.49  sup_given_eliminated:                   0
% 7.01/1.49  comparisons_done:                       0
% 7.01/1.49  comparisons_avoided:                    1
% 7.01/1.49  
% 7.01/1.49  ------ Simplifications
% 7.01/1.49  
% 7.01/1.49  
% 7.01/1.49  sim_fw_subset_subsumed:                 6
% 7.01/1.49  sim_bw_subset_subsumed:                 3
% 7.01/1.49  sim_fw_subsumed:                        0
% 7.01/1.49  sim_bw_subsumed:                        0
% 7.01/1.49  sim_fw_subsumption_res:                 0
% 7.01/1.49  sim_bw_subsumption_res:                 0
% 7.01/1.49  sim_tautology_del:                      0
% 7.01/1.49  sim_eq_tautology_del:                   91
% 7.01/1.49  sim_eq_res_simp:                        0
% 7.01/1.49  sim_fw_demodulated:                     2
% 7.01/1.49  sim_bw_demodulated:                     6
% 7.01/1.49  sim_light_normalised:                   96
% 7.01/1.49  sim_joinable_taut:                      0
% 7.01/1.49  sim_joinable_simp:                      0
% 7.01/1.49  sim_ac_normalised:                      0
% 7.01/1.49  sim_smt_subsumption:                    0
% 7.01/1.49  
%------------------------------------------------------------------------------
