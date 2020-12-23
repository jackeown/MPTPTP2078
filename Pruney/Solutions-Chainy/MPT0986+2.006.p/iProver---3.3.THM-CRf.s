%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:54 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 240 expanded)
%              Number of clauses        :   62 (  82 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   23
%              Number of atoms          :  469 (1549 expanded)
%              Number of equality atoms :  196 ( 525 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f19,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
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
    inference(definition_folding,[],[f13,f19])).

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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f27])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f66,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X2,X0)
            & v2_funct_1(X3) )
         => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & v2_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5
      & k1_xboole_0 != sK4
      & r2_hidden(sK5,sK3)
      & v2_funct_1(sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5
    & k1_xboole_0 != sK4
    & r2_hidden(sK5,sK3)
    & v2_funct_1(sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f30])).

fof(f58,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(nnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_510,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_511,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_515,plain,
    ( ~ v1_funct_1(k2_funct_1(sK6))
    | ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_29])).

cnf(c_516,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_515])).

cnf(c_1493,plain,
    ( ~ r2_hidden(X0_51,k1_relat_1(sK6))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_1511,plain,
    ( ~ r2_hidden(X0_51,k1_relat_1(sK6))
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1493])).

cnf(c_1947,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
    | r2_hidden(X0_51,k1_relat_1(sK6)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1511])).

cnf(c_30,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1512,plain,
    ( ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ v1_relat_1(sK6)
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1493])).

cnf(c_1580,plain,
    ( v1_funct_1(k2_funct_1(sK6)) != iProver_top
    | v1_relat_1(k2_funct_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1512])).

cnf(c_1581,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
    | r2_hidden(X0_51,k1_relat_1(sK6)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1511])).

cnf(c_1517,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_2171,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1506,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | v1_relat_1(k2_funct_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2173,plain,
    ( ~ v1_funct_1(sK6)
    | v1_relat_1(k2_funct_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_2174,plain,
    ( v1_funct_1(sK6) != iProver_top
    | v1_relat_1(k2_funct_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2173])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1507,plain,
    ( ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_1(X0_49))
    | ~ v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2176,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_2177,plain,
    ( v1_funct_1(k2_funct_1(sK6)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2176])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_324,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_27])).

cnf(c_325,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1496,plain,
    ( ~ v1_relat_1(X0_49)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_325])).

cnf(c_2162,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_2259,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_2260,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2259])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1508,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2325,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_2326,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2325])).

cnf(c_2480,plain,
    ( r2_hidden(X0_51,k1_relat_1(sK6)) != iProver_top
    | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1947,c_30,c_1580,c_1581,c_2171,c_2174,c_2177,c_2260,c_2326])).

cnf(c_2481,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
    | r2_hidden(X0_51,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2480])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_375,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_376,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_1495,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_relset_1(X0_49,X1_49,sK6) = k1_relat_1(sK6) ),
    inference(subtyping,[status(esa)],[c_376])).

cnf(c_2193,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_1495])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_339,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_340,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_730,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK3 != X0
    | sK4 != X1
    | sK6 != sK6
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_340])).

cnf(c_731,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_732,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_relset_1(sK3,sK4,sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_24])).

cnf(c_733,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(renaming,[status(thm)],[c_732])).

cnf(c_1096,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_733])).

cnf(c_1485,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3 ),
    inference(subtyping,[status(esa)],[c_1096])).

cnf(c_2306,plain,
    ( k1_relat_1(sK6) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2193,c_1485])).

cnf(c_2486,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
    | r2_hidden(X0_51,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2481,c_2306])).

cnf(c_2490,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) = sK5
    | r2_hidden(sK5,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2486])).

cnf(c_23,negated_conjecture,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1500,negated_conjecture,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_34,plain,
    ( r2_hidden(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2490,c_1500,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.76/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.76/0.99  
% 1.76/0.99  ------  iProver source info
% 1.76/0.99  
% 1.76/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.76/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.76/0.99  git: non_committed_changes: false
% 1.76/0.99  git: last_make_outside_of_git: false
% 1.76/0.99  
% 1.76/0.99  ------ 
% 1.76/0.99  
% 1.76/0.99  ------ Input Options
% 1.76/0.99  
% 1.76/0.99  --out_options                           all
% 1.76/0.99  --tptp_safe_out                         true
% 1.76/0.99  --problem_path                          ""
% 1.76/0.99  --include_path                          ""
% 1.76/0.99  --clausifier                            res/vclausify_rel
% 1.76/0.99  --clausifier_options                    --mode clausify
% 1.76/0.99  --stdin                                 false
% 1.76/0.99  --stats_out                             all
% 1.76/0.99  
% 1.76/0.99  ------ General Options
% 1.76/0.99  
% 1.76/0.99  --fof                                   false
% 1.76/0.99  --time_out_real                         305.
% 1.76/0.99  --time_out_virtual                      -1.
% 1.76/0.99  --symbol_type_check                     false
% 1.76/0.99  --clausify_out                          false
% 1.76/0.99  --sig_cnt_out                           false
% 1.76/0.99  --trig_cnt_out                          false
% 1.76/0.99  --trig_cnt_out_tolerance                1.
% 1.76/0.99  --trig_cnt_out_sk_spl                   false
% 1.76/0.99  --abstr_cl_out                          false
% 1.76/0.99  
% 1.76/0.99  ------ Global Options
% 1.76/0.99  
% 1.76/0.99  --schedule                              default
% 1.76/0.99  --add_important_lit                     false
% 1.76/0.99  --prop_solver_per_cl                    1000
% 1.76/0.99  --min_unsat_core                        false
% 1.76/0.99  --soft_assumptions                      false
% 1.76/0.99  --soft_lemma_size                       3
% 1.76/0.99  --prop_impl_unit_size                   0
% 1.76/0.99  --prop_impl_unit                        []
% 1.76/0.99  --share_sel_clauses                     true
% 1.76/0.99  --reset_solvers                         false
% 1.76/0.99  --bc_imp_inh                            [conj_cone]
% 1.76/0.99  --conj_cone_tolerance                   3.
% 1.76/0.99  --extra_neg_conj                        none
% 1.76/0.99  --large_theory_mode                     true
% 1.76/0.99  --prolific_symb_bound                   200
% 1.76/0.99  --lt_threshold                          2000
% 1.76/0.99  --clause_weak_htbl                      true
% 1.76/0.99  --gc_record_bc_elim                     false
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing Options
% 1.76/0.99  
% 1.76/0.99  --preprocessing_flag                    true
% 1.76/0.99  --time_out_prep_mult                    0.1
% 1.76/0.99  --splitting_mode                        input
% 1.76/0.99  --splitting_grd                         true
% 1.76/0.99  --splitting_cvd                         false
% 1.76/0.99  --splitting_cvd_svl                     false
% 1.76/0.99  --splitting_nvd                         32
% 1.76/0.99  --sub_typing                            true
% 1.76/0.99  --prep_gs_sim                           true
% 1.76/0.99  --prep_unflatten                        true
% 1.76/0.99  --prep_res_sim                          true
% 1.76/0.99  --prep_upred                            true
% 1.76/0.99  --prep_sem_filter                       exhaustive
% 1.76/0.99  --prep_sem_filter_out                   false
% 1.76/0.99  --pred_elim                             true
% 1.76/0.99  --res_sim_input                         true
% 1.76/0.99  --eq_ax_congr_red                       true
% 1.76/0.99  --pure_diseq_elim                       true
% 1.76/0.99  --brand_transform                       false
% 1.76/0.99  --non_eq_to_eq                          false
% 1.76/0.99  --prep_def_merge                        true
% 1.76/0.99  --prep_def_merge_prop_impl              false
% 1.76/0.99  --prep_def_merge_mbd                    true
% 1.76/0.99  --prep_def_merge_tr_red                 false
% 1.76/0.99  --prep_def_merge_tr_cl                  false
% 1.76/0.99  --smt_preprocessing                     true
% 1.76/0.99  --smt_ac_axioms                         fast
% 1.76/0.99  --preprocessed_out                      false
% 1.76/0.99  --preprocessed_stats                    false
% 1.76/0.99  
% 1.76/0.99  ------ Abstraction refinement Options
% 1.76/0.99  
% 1.76/0.99  --abstr_ref                             []
% 1.76/0.99  --abstr_ref_prep                        false
% 1.76/0.99  --abstr_ref_until_sat                   false
% 1.76/0.99  --abstr_ref_sig_restrict                funpre
% 1.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/0.99  --abstr_ref_under                       []
% 1.76/0.99  
% 1.76/0.99  ------ SAT Options
% 1.76/0.99  
% 1.76/0.99  --sat_mode                              false
% 1.76/0.99  --sat_fm_restart_options                ""
% 1.76/0.99  --sat_gr_def                            false
% 1.76/0.99  --sat_epr_types                         true
% 1.76/0.99  --sat_non_cyclic_types                  false
% 1.76/0.99  --sat_finite_models                     false
% 1.76/0.99  --sat_fm_lemmas                         false
% 1.76/0.99  --sat_fm_prep                           false
% 1.76/0.99  --sat_fm_uc_incr                        true
% 1.76/0.99  --sat_out_model                         small
% 1.76/0.99  --sat_out_clauses                       false
% 1.76/0.99  
% 1.76/0.99  ------ QBF Options
% 1.76/0.99  
% 1.76/0.99  --qbf_mode                              false
% 1.76/0.99  --qbf_elim_univ                         false
% 1.76/0.99  --qbf_dom_inst                          none
% 1.76/0.99  --qbf_dom_pre_inst                      false
% 1.76/0.99  --qbf_sk_in                             false
% 1.76/0.99  --qbf_pred_elim                         true
% 1.76/0.99  --qbf_split                             512
% 1.76/0.99  
% 1.76/0.99  ------ BMC1 Options
% 1.76/0.99  
% 1.76/0.99  --bmc1_incremental                      false
% 1.76/0.99  --bmc1_axioms                           reachable_all
% 1.76/0.99  --bmc1_min_bound                        0
% 1.76/0.99  --bmc1_max_bound                        -1
% 1.76/0.99  --bmc1_max_bound_default                -1
% 1.76/0.99  --bmc1_symbol_reachability              true
% 1.76/0.99  --bmc1_property_lemmas                  false
% 1.76/0.99  --bmc1_k_induction                      false
% 1.76/0.99  --bmc1_non_equiv_states                 false
% 1.76/0.99  --bmc1_deadlock                         false
% 1.76/0.99  --bmc1_ucm                              false
% 1.76/0.99  --bmc1_add_unsat_core                   none
% 1.76/0.99  --bmc1_unsat_core_children              false
% 1.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/0.99  --bmc1_out_stat                         full
% 1.76/0.99  --bmc1_ground_init                      false
% 1.76/0.99  --bmc1_pre_inst_next_state              false
% 1.76/0.99  --bmc1_pre_inst_state                   false
% 1.76/0.99  --bmc1_pre_inst_reach_state             false
% 1.76/0.99  --bmc1_out_unsat_core                   false
% 1.76/0.99  --bmc1_aig_witness_out                  false
% 1.76/0.99  --bmc1_verbose                          false
% 1.76/0.99  --bmc1_dump_clauses_tptp                false
% 1.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.76/0.99  --bmc1_dump_file                        -
% 1.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.76/0.99  --bmc1_ucm_extend_mode                  1
% 1.76/0.99  --bmc1_ucm_init_mode                    2
% 1.76/0.99  --bmc1_ucm_cone_mode                    none
% 1.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.76/0.99  --bmc1_ucm_relax_model                  4
% 1.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/0.99  --bmc1_ucm_layered_model                none
% 1.76/0.99  --bmc1_ucm_max_lemma_size               10
% 1.76/0.99  
% 1.76/0.99  ------ AIG Options
% 1.76/0.99  
% 1.76/0.99  --aig_mode                              false
% 1.76/0.99  
% 1.76/0.99  ------ Instantiation Options
% 1.76/0.99  
% 1.76/0.99  --instantiation_flag                    true
% 1.76/0.99  --inst_sos_flag                         false
% 1.76/0.99  --inst_sos_phase                        true
% 1.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/0.99  --inst_lit_sel_side                     num_symb
% 1.76/0.99  --inst_solver_per_active                1400
% 1.76/0.99  --inst_solver_calls_frac                1.
% 1.76/0.99  --inst_passive_queue_type               priority_queues
% 1.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/0.99  --inst_passive_queues_freq              [25;2]
% 1.76/0.99  --inst_dismatching                      true
% 1.76/0.99  --inst_eager_unprocessed_to_passive     true
% 1.76/0.99  --inst_prop_sim_given                   true
% 1.76/0.99  --inst_prop_sim_new                     false
% 1.76/0.99  --inst_subs_new                         false
% 1.76/0.99  --inst_eq_res_simp                      false
% 1.76/0.99  --inst_subs_given                       false
% 1.76/0.99  --inst_orphan_elimination               true
% 1.76/0.99  --inst_learning_loop_flag               true
% 1.76/0.99  --inst_learning_start                   3000
% 1.76/0.99  --inst_learning_factor                  2
% 1.76/0.99  --inst_start_prop_sim_after_learn       3
% 1.76/0.99  --inst_sel_renew                        solver
% 1.76/0.99  --inst_lit_activity_flag                true
% 1.76/0.99  --inst_restr_to_given                   false
% 1.76/0.99  --inst_activity_threshold               500
% 1.76/0.99  --inst_out_proof                        true
% 1.76/0.99  
% 1.76/0.99  ------ Resolution Options
% 1.76/0.99  
% 1.76/0.99  --resolution_flag                       true
% 1.76/0.99  --res_lit_sel                           adaptive
% 1.76/0.99  --res_lit_sel_side                      none
% 1.76/0.99  --res_ordering                          kbo
% 1.76/0.99  --res_to_prop_solver                    active
% 1.76/0.99  --res_prop_simpl_new                    false
% 1.76/0.99  --res_prop_simpl_given                  true
% 1.76/0.99  --res_passive_queue_type                priority_queues
% 1.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/0.99  --res_passive_queues_freq               [15;5]
% 1.76/0.99  --res_forward_subs                      full
% 1.76/0.99  --res_backward_subs                     full
% 1.76/0.99  --res_forward_subs_resolution           true
% 1.76/0.99  --res_backward_subs_resolution          true
% 1.76/0.99  --res_orphan_elimination                true
% 1.76/0.99  --res_time_limit                        2.
% 1.76/0.99  --res_out_proof                         true
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Options
% 1.76/0.99  
% 1.76/0.99  --superposition_flag                    true
% 1.76/0.99  --sup_passive_queue_type                priority_queues
% 1.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.76/0.99  --demod_completeness_check              fast
% 1.76/0.99  --demod_use_ground                      true
% 1.76/0.99  --sup_to_prop_solver                    passive
% 1.76/0.99  --sup_prop_simpl_new                    true
% 1.76/0.99  --sup_prop_simpl_given                  true
% 1.76/0.99  --sup_fun_splitting                     false
% 1.76/0.99  --sup_smt_interval                      50000
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Simplification Setup
% 1.76/0.99  
% 1.76/0.99  --sup_indices_passive                   []
% 1.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_full_bw                           [BwDemod]
% 1.76/0.99  --sup_immed_triv                        [TrivRules]
% 1.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_immed_bw_main                     []
% 1.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  
% 1.76/0.99  ------ Combination Options
% 1.76/0.99  
% 1.76/0.99  --comb_res_mult                         3
% 1.76/0.99  --comb_sup_mult                         2
% 1.76/0.99  --comb_inst_mult                        10
% 1.76/0.99  
% 1.76/0.99  ------ Debug Options
% 1.76/0.99  
% 1.76/0.99  --dbg_backtrace                         false
% 1.76/0.99  --dbg_dump_prop_clauses                 false
% 1.76/0.99  --dbg_dump_prop_clauses_file            -
% 1.76/0.99  --dbg_out_stat                          false
% 1.76/0.99  ------ Parsing...
% 1.76/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.76/0.99  ------ Proving...
% 1.76/0.99  ------ Problem Properties 
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  clauses                                 27
% 1.76/0.99  conjectures                             4
% 1.76/0.99  EPR                                     3
% 1.76/0.99  Horn                                    22
% 1.76/0.99  unary                                   6
% 1.76/0.99  binary                                  6
% 1.76/0.99  lits                                    80
% 1.76/0.99  lits eq                                 25
% 1.76/0.99  fd_pure                                 0
% 1.76/0.99  fd_pseudo                               0
% 1.76/0.99  fd_cond                                 3
% 1.76/0.99  fd_pseudo_cond                          1
% 1.76/0.99  AC symbols                              0
% 1.76/0.99  
% 1.76/0.99  ------ Schedule dynamic 5 is on 
% 1.76/0.99  
% 1.76/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  ------ 
% 1.76/0.99  Current options:
% 1.76/0.99  ------ 
% 1.76/0.99  
% 1.76/0.99  ------ Input Options
% 1.76/0.99  
% 1.76/0.99  --out_options                           all
% 1.76/0.99  --tptp_safe_out                         true
% 1.76/0.99  --problem_path                          ""
% 1.76/0.99  --include_path                          ""
% 1.76/0.99  --clausifier                            res/vclausify_rel
% 1.76/0.99  --clausifier_options                    --mode clausify
% 1.76/0.99  --stdin                                 false
% 1.76/0.99  --stats_out                             all
% 1.76/0.99  
% 1.76/0.99  ------ General Options
% 1.76/0.99  
% 1.76/0.99  --fof                                   false
% 1.76/0.99  --time_out_real                         305.
% 1.76/0.99  --time_out_virtual                      -1.
% 1.76/0.99  --symbol_type_check                     false
% 1.76/0.99  --clausify_out                          false
% 1.76/0.99  --sig_cnt_out                           false
% 1.76/0.99  --trig_cnt_out                          false
% 1.76/0.99  --trig_cnt_out_tolerance                1.
% 1.76/0.99  --trig_cnt_out_sk_spl                   false
% 1.76/0.99  --abstr_cl_out                          false
% 1.76/0.99  
% 1.76/0.99  ------ Global Options
% 1.76/0.99  
% 1.76/0.99  --schedule                              default
% 1.76/0.99  --add_important_lit                     false
% 1.76/0.99  --prop_solver_per_cl                    1000
% 1.76/0.99  --min_unsat_core                        false
% 1.76/0.99  --soft_assumptions                      false
% 1.76/0.99  --soft_lemma_size                       3
% 1.76/0.99  --prop_impl_unit_size                   0
% 1.76/0.99  --prop_impl_unit                        []
% 1.76/0.99  --share_sel_clauses                     true
% 1.76/0.99  --reset_solvers                         false
% 1.76/0.99  --bc_imp_inh                            [conj_cone]
% 1.76/0.99  --conj_cone_tolerance                   3.
% 1.76/0.99  --extra_neg_conj                        none
% 1.76/0.99  --large_theory_mode                     true
% 1.76/0.99  --prolific_symb_bound                   200
% 1.76/0.99  --lt_threshold                          2000
% 1.76/0.99  --clause_weak_htbl                      true
% 1.76/0.99  --gc_record_bc_elim                     false
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing Options
% 1.76/0.99  
% 1.76/0.99  --preprocessing_flag                    true
% 1.76/0.99  --time_out_prep_mult                    0.1
% 1.76/0.99  --splitting_mode                        input
% 1.76/0.99  --splitting_grd                         true
% 1.76/0.99  --splitting_cvd                         false
% 1.76/0.99  --splitting_cvd_svl                     false
% 1.76/0.99  --splitting_nvd                         32
% 1.76/0.99  --sub_typing                            true
% 1.76/0.99  --prep_gs_sim                           true
% 1.76/0.99  --prep_unflatten                        true
% 1.76/0.99  --prep_res_sim                          true
% 1.76/0.99  --prep_upred                            true
% 1.76/0.99  --prep_sem_filter                       exhaustive
% 1.76/0.99  --prep_sem_filter_out                   false
% 1.76/0.99  --pred_elim                             true
% 1.76/0.99  --res_sim_input                         true
% 1.76/0.99  --eq_ax_congr_red                       true
% 1.76/0.99  --pure_diseq_elim                       true
% 1.76/0.99  --brand_transform                       false
% 1.76/0.99  --non_eq_to_eq                          false
% 1.76/0.99  --prep_def_merge                        true
% 1.76/0.99  --prep_def_merge_prop_impl              false
% 1.76/0.99  --prep_def_merge_mbd                    true
% 1.76/0.99  --prep_def_merge_tr_red                 false
% 1.76/0.99  --prep_def_merge_tr_cl                  false
% 1.76/0.99  --smt_preprocessing                     true
% 1.76/0.99  --smt_ac_axioms                         fast
% 1.76/0.99  --preprocessed_out                      false
% 1.76/0.99  --preprocessed_stats                    false
% 1.76/0.99  
% 1.76/0.99  ------ Abstraction refinement Options
% 1.76/0.99  
% 1.76/0.99  --abstr_ref                             []
% 1.76/0.99  --abstr_ref_prep                        false
% 1.76/0.99  --abstr_ref_until_sat                   false
% 1.76/0.99  --abstr_ref_sig_restrict                funpre
% 1.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/0.99  --abstr_ref_under                       []
% 1.76/0.99  
% 1.76/0.99  ------ SAT Options
% 1.76/0.99  
% 1.76/0.99  --sat_mode                              false
% 1.76/0.99  --sat_fm_restart_options                ""
% 1.76/0.99  --sat_gr_def                            false
% 1.76/0.99  --sat_epr_types                         true
% 1.76/0.99  --sat_non_cyclic_types                  false
% 1.76/0.99  --sat_finite_models                     false
% 1.76/0.99  --sat_fm_lemmas                         false
% 1.76/0.99  --sat_fm_prep                           false
% 1.76/0.99  --sat_fm_uc_incr                        true
% 1.76/0.99  --sat_out_model                         small
% 1.76/0.99  --sat_out_clauses                       false
% 1.76/0.99  
% 1.76/0.99  ------ QBF Options
% 1.76/0.99  
% 1.76/0.99  --qbf_mode                              false
% 1.76/0.99  --qbf_elim_univ                         false
% 1.76/0.99  --qbf_dom_inst                          none
% 1.76/0.99  --qbf_dom_pre_inst                      false
% 1.76/0.99  --qbf_sk_in                             false
% 1.76/0.99  --qbf_pred_elim                         true
% 1.76/0.99  --qbf_split                             512
% 1.76/0.99  
% 1.76/0.99  ------ BMC1 Options
% 1.76/0.99  
% 1.76/0.99  --bmc1_incremental                      false
% 1.76/0.99  --bmc1_axioms                           reachable_all
% 1.76/0.99  --bmc1_min_bound                        0
% 1.76/0.99  --bmc1_max_bound                        -1
% 1.76/0.99  --bmc1_max_bound_default                -1
% 1.76/0.99  --bmc1_symbol_reachability              true
% 1.76/0.99  --bmc1_property_lemmas                  false
% 1.76/0.99  --bmc1_k_induction                      false
% 1.76/0.99  --bmc1_non_equiv_states                 false
% 1.76/0.99  --bmc1_deadlock                         false
% 1.76/0.99  --bmc1_ucm                              false
% 1.76/0.99  --bmc1_add_unsat_core                   none
% 1.76/0.99  --bmc1_unsat_core_children              false
% 1.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/0.99  --bmc1_out_stat                         full
% 1.76/0.99  --bmc1_ground_init                      false
% 1.76/0.99  --bmc1_pre_inst_next_state              false
% 1.76/0.99  --bmc1_pre_inst_state                   false
% 1.76/0.99  --bmc1_pre_inst_reach_state             false
% 1.76/0.99  --bmc1_out_unsat_core                   false
% 1.76/0.99  --bmc1_aig_witness_out                  false
% 1.76/0.99  --bmc1_verbose                          false
% 1.76/0.99  --bmc1_dump_clauses_tptp                false
% 1.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.76/0.99  --bmc1_dump_file                        -
% 1.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.76/0.99  --bmc1_ucm_extend_mode                  1
% 1.76/0.99  --bmc1_ucm_init_mode                    2
% 1.76/0.99  --bmc1_ucm_cone_mode                    none
% 1.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.76/0.99  --bmc1_ucm_relax_model                  4
% 1.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/0.99  --bmc1_ucm_layered_model                none
% 1.76/0.99  --bmc1_ucm_max_lemma_size               10
% 1.76/0.99  
% 1.76/0.99  ------ AIG Options
% 1.76/0.99  
% 1.76/0.99  --aig_mode                              false
% 1.76/0.99  
% 1.76/0.99  ------ Instantiation Options
% 1.76/0.99  
% 1.76/0.99  --instantiation_flag                    true
% 1.76/0.99  --inst_sos_flag                         false
% 1.76/0.99  --inst_sos_phase                        true
% 1.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/0.99  --inst_lit_sel_side                     none
% 1.76/0.99  --inst_solver_per_active                1400
% 1.76/0.99  --inst_solver_calls_frac                1.
% 1.76/0.99  --inst_passive_queue_type               priority_queues
% 1.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/0.99  --inst_passive_queues_freq              [25;2]
% 1.76/0.99  --inst_dismatching                      true
% 1.76/0.99  --inst_eager_unprocessed_to_passive     true
% 1.76/0.99  --inst_prop_sim_given                   true
% 1.76/0.99  --inst_prop_sim_new                     false
% 1.76/0.99  --inst_subs_new                         false
% 1.76/0.99  --inst_eq_res_simp                      false
% 1.76/0.99  --inst_subs_given                       false
% 1.76/0.99  --inst_orphan_elimination               true
% 1.76/0.99  --inst_learning_loop_flag               true
% 1.76/0.99  --inst_learning_start                   3000
% 1.76/0.99  --inst_learning_factor                  2
% 1.76/0.99  --inst_start_prop_sim_after_learn       3
% 1.76/0.99  --inst_sel_renew                        solver
% 1.76/0.99  --inst_lit_activity_flag                true
% 1.76/0.99  --inst_restr_to_given                   false
% 1.76/0.99  --inst_activity_threshold               500
% 1.76/0.99  --inst_out_proof                        true
% 1.76/0.99  
% 1.76/0.99  ------ Resolution Options
% 1.76/0.99  
% 1.76/0.99  --resolution_flag                       false
% 1.76/0.99  --res_lit_sel                           adaptive
% 1.76/0.99  --res_lit_sel_side                      none
% 1.76/0.99  --res_ordering                          kbo
% 1.76/0.99  --res_to_prop_solver                    active
% 1.76/0.99  --res_prop_simpl_new                    false
% 1.76/0.99  --res_prop_simpl_given                  true
% 1.76/0.99  --res_passive_queue_type                priority_queues
% 1.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/0.99  --res_passive_queues_freq               [15;5]
% 1.76/0.99  --res_forward_subs                      full
% 1.76/0.99  --res_backward_subs                     full
% 1.76/0.99  --res_forward_subs_resolution           true
% 1.76/0.99  --res_backward_subs_resolution          true
% 1.76/0.99  --res_orphan_elimination                true
% 1.76/0.99  --res_time_limit                        2.
% 1.76/0.99  --res_out_proof                         true
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Options
% 1.76/0.99  
% 1.76/0.99  --superposition_flag                    true
% 1.76/0.99  --sup_passive_queue_type                priority_queues
% 1.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.76/0.99  --demod_completeness_check              fast
% 1.76/0.99  --demod_use_ground                      true
% 1.76/0.99  --sup_to_prop_solver                    passive
% 1.76/0.99  --sup_prop_simpl_new                    true
% 1.76/0.99  --sup_prop_simpl_given                  true
% 1.76/0.99  --sup_fun_splitting                     false
% 1.76/0.99  --sup_smt_interval                      50000
% 1.76/0.99  
% 1.76/0.99  ------ Superposition Simplification Setup
% 1.76/0.99  
% 1.76/0.99  --sup_indices_passive                   []
% 1.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_full_bw                           [BwDemod]
% 1.76/0.99  --sup_immed_triv                        [TrivRules]
% 1.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_immed_bw_main                     []
% 1.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.99  
% 1.76/0.99  ------ Combination Options
% 1.76/0.99  
% 1.76/0.99  --comb_res_mult                         3
% 1.76/0.99  --comb_sup_mult                         2
% 1.76/0.99  --comb_inst_mult                        10
% 1.76/0.99  
% 1.76/0.99  ------ Debug Options
% 1.76/0.99  
% 1.76/0.99  --dbg_backtrace                         false
% 1.76/0.99  --dbg_dump_prop_clauses                 false
% 1.76/0.99  --dbg_dump_prop_clauses_file            -
% 1.76/0.99  --dbg_out_stat                          false
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  ------ Proving...
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  % SZS status Theorem for theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  fof(f4,axiom,(
% 1.76/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 1.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f12,plain,(
% 1.76/0.99    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f4])).
% 1.76/0.99  
% 1.76/0.99  fof(f13,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.99    inference(flattening,[],[f12])).
% 1.76/0.99  
% 1.76/0.99  fof(f19,plain,(
% 1.76/0.99    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 1.76/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.76/0.99  
% 1.76/0.99  fof(f20,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.99    inference(definition_folding,[],[f13,f19])).
% 1.76/0.99  
% 1.76/0.99  fof(f24,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.99    inference(nnf_transformation,[],[f20])).
% 1.76/0.99  
% 1.76/0.99  fof(f25,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.99    inference(flattening,[],[f24])).
% 1.76/0.99  
% 1.76/0.99  fof(f26,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | ? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.99    inference(rectify,[],[f25])).
% 1.76/0.99  
% 1.76/0.99  fof(f27,plain,(
% 1.76/0.99    ! [X1,X0] : (? [X2,X3] : (((k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) & k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X3,X0,X1)) => (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)))),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f28,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (((k2_funct_1(X0) = X1 | (((k1_funct_1(X1,sK1(X0,X1)) != sK2(X0,X1) | ~r2_hidden(sK1(X0,X1),k2_relat_1(X0))) & k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | ~sP0(sK1(X0,X1),sK2(X0,X1),X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (((k1_funct_1(X1,X4) = X5 & r2_hidden(X4,k2_relat_1(X0))) | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0))) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | k2_funct_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f27])).
% 1.76/0.99  
% 1.76/0.99  fof(f44,plain,(
% 1.76/0.99    ( ! [X4,X0,X5,X1] : (k1_funct_1(X1,X4) = X5 | k1_funct_1(X0,X5) != X4 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f28])).
% 1.76/0.99  
% 1.76/0.99  fof(f65,plain,(
% 1.76/0.99    ( ! [X0,X5,X1] : (k1_funct_1(X1,k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | k2_funct_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.99    inference(equality_resolution,[],[f44])).
% 1.76/0.99  
% 1.76/0.99  fof(f66,plain,(
% 1.76/0.99    ( ! [X0,X5] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5 | ~r2_hidden(X5,k1_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.99    inference(equality_resolution,[],[f65])).
% 1.76/0.99  
% 1.76/0.99  fof(f7,conjecture,(
% 1.76/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f8,negated_conjecture,(
% 1.76/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.76/0.99    inference(negated_conjecture,[],[f7])).
% 1.76/0.99  
% 1.76/0.99  fof(f17,plain,(
% 1.76/0.99    ? [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1) & (r2_hidden(X2,X0) & v2_funct_1(X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.76/0.99    inference(ennf_transformation,[],[f8])).
% 1.76/0.99  
% 1.76/0.99  fof(f18,plain,(
% 1.76/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.76/0.99    inference(flattening,[],[f17])).
% 1.76/0.99  
% 1.76/0.99  fof(f30,plain,(
% 1.76/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5 & k1_xboole_0 != sK4 & r2_hidden(sK5,sK3) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 1.76/0.99    introduced(choice_axiom,[])).
% 1.76/0.99  
% 1.76/0.99  fof(f31,plain,(
% 1.76/0.99    k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5 & k1_xboole_0 != sK4 & r2_hidden(sK5,sK3) & v2_funct_1(sK6) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 1.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f18,f30])).
% 1.76/0.99  
% 1.76/0.99  fof(f58,plain,(
% 1.76/0.99    v2_funct_1(sK6)),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f55,plain,(
% 1.76/0.99    v1_funct_1(sK6)),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f3,axiom,(
% 1.76/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f10,plain,(
% 1.76/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.76/0.99    inference(ennf_transformation,[],[f3])).
% 1.76/0.99  
% 1.76/0.99  fof(f11,plain,(
% 1.76/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.76/0.99    inference(flattening,[],[f10])).
% 1.76/0.99  
% 1.76/0.99  fof(f34,plain,(
% 1.76/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f11])).
% 1.76/0.99  
% 1.76/0.99  fof(f35,plain,(
% 1.76/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f11])).
% 1.76/0.99  
% 1.76/0.99  fof(f1,axiom,(
% 1.76/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f9,plain,(
% 1.76/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.76/0.99    inference(ennf_transformation,[],[f1])).
% 1.76/0.99  
% 1.76/0.99  fof(f32,plain,(
% 1.76/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.76/0.99    inference(cnf_transformation,[],[f9])).
% 1.76/0.99  
% 1.76/0.99  fof(f57,plain,(
% 1.76/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f2,axiom,(
% 1.76/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f33,plain,(
% 1.76/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.76/0.99    inference(cnf_transformation,[],[f2])).
% 1.76/0.99  
% 1.76/0.99  fof(f5,axiom,(
% 1.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f14,plain,(
% 1.76/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.99    inference(ennf_transformation,[],[f5])).
% 1.76/0.99  
% 1.76/0.99  fof(f48,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/0.99    inference(cnf_transformation,[],[f14])).
% 1.76/0.99  
% 1.76/0.99  fof(f56,plain,(
% 1.76/0.99    v1_funct_2(sK6,sK3,sK4)),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f6,axiom,(
% 1.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.76/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/0.99  
% 1.76/0.99  fof(f15,plain,(
% 1.76/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.99    inference(ennf_transformation,[],[f6])).
% 1.76/0.99  
% 1.76/0.99  fof(f16,plain,(
% 1.76/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.99    inference(flattening,[],[f15])).
% 1.76/0.99  
% 1.76/0.99  fof(f29,plain,(
% 1.76/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.76/0.99    inference(nnf_transformation,[],[f16])).
% 1.76/0.99  
% 1.76/0.99  fof(f49,plain,(
% 1.76/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.76/0.99    inference(cnf_transformation,[],[f29])).
% 1.76/0.99  
% 1.76/0.99  fof(f60,plain,(
% 1.76/0.99    k1_xboole_0 != sK4),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f61,plain,(
% 1.76/0.99    k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  fof(f59,plain,(
% 1.76/0.99    r2_hidden(sK5,sK3)),
% 1.76/0.99    inference(cnf_transformation,[],[f31])).
% 1.76/0.99  
% 1.76/0.99  cnf(c_12,plain,
% 1.76/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.76/0.99      | ~ v2_funct_1(X1)
% 1.76/0.99      | ~ v1_funct_1(X1)
% 1.76/0.99      | ~ v1_funct_1(k2_funct_1(X1))
% 1.76/0.99      | ~ v1_relat_1(X1)
% 1.76/0.99      | ~ v1_relat_1(k2_funct_1(X1))
% 1.76/0.99      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 1.76/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_26,negated_conjecture,
% 1.76/0.99      ( v2_funct_1(sK6) ),
% 1.76/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_510,plain,
% 1.76/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.76/0.99      | ~ v1_funct_1(X1)
% 1.76/0.99      | ~ v1_funct_1(k2_funct_1(X1))
% 1.76/0.99      | ~ v1_relat_1(X1)
% 1.76/0.99      | ~ v1_relat_1(k2_funct_1(X1))
% 1.76/0.99      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 1.76/0.99      | sK6 != X1 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_511,plain,
% 1.76/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 1.76/0.99      | ~ v1_funct_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_funct_1(sK6)
% 1.76/0.99      | ~ v1_relat_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(sK6)
% 1.76/0.99      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_510]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_29,negated_conjecture,
% 1.76/0.99      ( v1_funct_1(sK6) ),
% 1.76/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_515,plain,
% 1.76/0.99      ( ~ v1_funct_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ r2_hidden(X0,k1_relat_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(sK6)
% 1.76/0.99      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_511,c_29]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_516,plain,
% 1.76/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 1.76/0.99      | ~ v1_funct_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(sK6)
% 1.76/0.99      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_515]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1493,plain,
% 1.76/0.99      ( ~ r2_hidden(X0_51,k1_relat_1(sK6))
% 1.76/0.99      | ~ v1_funct_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(sK6)
% 1.76/0.99      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51 ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_516]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1511,plain,
% 1.76/0.99      ( ~ r2_hidden(X0_51,k1_relat_1(sK6))
% 1.76/0.99      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
% 1.76/0.99      | ~ sP1_iProver_split ),
% 1.76/0.99      inference(splitting,
% 1.76/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.76/0.99                [c_1493]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1947,plain,
% 1.76/0.99      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
% 1.76/0.99      | r2_hidden(X0_51,k1_relat_1(sK6)) != iProver_top
% 1.76/0.99      | sP1_iProver_split != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1511]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_30,plain,
% 1.76/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1512,plain,
% 1.76/0.99      ( ~ v1_funct_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(sK6)
% 1.76/0.99      | sP1_iProver_split ),
% 1.76/0.99      inference(splitting,
% 1.76/0.99                [splitting(split),new_symbols(definition,[])],
% 1.76/0.99                [c_1493]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1580,plain,
% 1.76/0.99      ( v1_funct_1(k2_funct_1(sK6)) != iProver_top
% 1.76/0.99      | v1_relat_1(k2_funct_1(sK6)) != iProver_top
% 1.76/0.99      | v1_relat_1(sK6) != iProver_top
% 1.76/0.99      | sP1_iProver_split = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1512]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1581,plain,
% 1.76/0.99      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
% 1.76/0.99      | r2_hidden(X0_51,k1_relat_1(sK6)) != iProver_top
% 1.76/0.99      | sP1_iProver_split != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_1511]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1517,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2171,plain,
% 1.76/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_1517]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_3,plain,
% 1.76/0.99      ( ~ v1_funct_1(X0)
% 1.76/0.99      | ~ v1_relat_1(X0)
% 1.76/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1506,plain,
% 1.76/0.99      ( ~ v1_funct_1(X0_49)
% 1.76/0.99      | ~ v1_relat_1(X0_49)
% 1.76/0.99      | v1_relat_1(k2_funct_1(X0_49)) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2173,plain,
% 1.76/0.99      ( ~ v1_funct_1(sK6)
% 1.76/0.99      | v1_relat_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_relat_1(sK6) ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_1506]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2174,plain,
% 1.76/0.99      ( v1_funct_1(sK6) != iProver_top
% 1.76/0.99      | v1_relat_1(k2_funct_1(sK6)) = iProver_top
% 1.76/0.99      | v1_relat_1(sK6) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2173]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2,plain,
% 1.76/0.99      ( ~ v1_funct_1(X0)
% 1.76/0.99      | v1_funct_1(k2_funct_1(X0))
% 1.76/0.99      | ~ v1_relat_1(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1507,plain,
% 1.76/0.99      ( ~ v1_funct_1(X0_49)
% 1.76/0.99      | v1_funct_1(k2_funct_1(X0_49))
% 1.76/0.99      | ~ v1_relat_1(X0_49) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2176,plain,
% 1.76/0.99      ( v1_funct_1(k2_funct_1(sK6))
% 1.76/0.99      | ~ v1_funct_1(sK6)
% 1.76/0.99      | ~ v1_relat_1(sK6) ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_1507]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2177,plain,
% 1.76/0.99      ( v1_funct_1(k2_funct_1(sK6)) = iProver_top
% 1.76/0.99      | v1_funct_1(sK6) != iProver_top
% 1.76/0.99      | v1_relat_1(sK6) != iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2176]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_0,plain,
% 1.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.76/0.99      | ~ v1_relat_1(X1)
% 1.76/0.99      | v1_relat_1(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_27,negated_conjecture,
% 1.76/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 1.76/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_324,plain,
% 1.76/0.99      ( ~ v1_relat_1(X0)
% 1.76/0.99      | v1_relat_1(X1)
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
% 1.76/0.99      | sK6 != X1 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_325,plain,
% 1.76/0.99      ( ~ v1_relat_1(X0)
% 1.76/0.99      | v1_relat_1(sK6)
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_324]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1496,plain,
% 1.76/0.99      ( ~ v1_relat_1(X0_49)
% 1.76/0.99      | v1_relat_1(sK6)
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0_49) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_325]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2162,plain,
% 1.76/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0_49,X1_49))
% 1.76/0.99      | v1_relat_1(sK6)
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_1496]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2259,plain,
% 1.76/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | v1_relat_1(sK6)
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_2162]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2260,plain,
% 1.76/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 1.76/0.99      | v1_relat_1(sK6) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2259]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1,plain,
% 1.76/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.76/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1508,plain,
% 1.76/0.99      ( v1_relat_1(k2_zfmisc_1(X0_49,X1_49)) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2325,plain,
% 1.76/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_1508]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2326,plain,
% 1.76/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_2325]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2480,plain,
% 1.76/0.99      ( r2_hidden(X0_51,k1_relat_1(sK6)) != iProver_top
% 1.76/0.99      | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51 ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_1947,c_30,c_1580,c_1581,c_2171,c_2174,c_2177,c_2260,
% 1.76/0.99                 c_2326]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2481,plain,
% 1.76/0.99      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
% 1.76/0.99      | r2_hidden(X0_51,k1_relat_1(sK6)) != iProver_top ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_2480]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_16,plain,
% 1.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.76/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_375,plain,
% 1.76/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | sK6 != X2 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_376,plain,
% 1.76/0.99      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_375]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1495,plain,
% 1.76/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | k1_relset_1(X0_49,X1_49,sK6) = k1_relat_1(sK6) ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_376]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2193,plain,
% 1.76/0.99      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 1.76/0.99      inference(equality_resolution,[status(thm)],[c_1495]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_28,negated_conjecture,
% 1.76/0.99      ( v1_funct_2(sK6,sK3,sK4) ),
% 1.76/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_22,plain,
% 1.76/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.76/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.76/0.99      | k1_xboole_0 = X2 ),
% 1.76/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_339,plain,
% 1.76/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 1.76/0.99      | k1_relset_1(X1,X2,X0) = X1
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | sK6 != X0
% 1.76/0.99      | k1_xboole_0 = X2 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_340,plain,
% 1.76/0.99      ( ~ v1_funct_2(sK6,X0,X1)
% 1.76/0.99      | k1_relset_1(X0,X1,sK6) = X0
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | k1_xboole_0 = X1 ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_730,plain,
% 1.76/0.99      ( k1_relset_1(X0,X1,sK6) = X0
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | sK3 != X0
% 1.76/0.99      | sK4 != X1
% 1.76/0.99      | sK6 != sK6
% 1.76/0.99      | k1_xboole_0 = X1 ),
% 1.76/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_340]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_731,plain,
% 1.76/0.99      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | k1_xboole_0 = sK4 ),
% 1.76/0.99      inference(unflattening,[status(thm)],[c_730]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_24,negated_conjecture,
% 1.76/0.99      ( k1_xboole_0 != sK4 ),
% 1.76/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_732,plain,
% 1.76/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 1.76/0.99      | k1_relset_1(sK3,sK4,sK6) = sK3 ),
% 1.76/0.99      inference(global_propositional_subsumption,
% 1.76/0.99                [status(thm)],
% 1.76/0.99                [c_731,c_24]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_733,plain,
% 1.76/0.99      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 1.76/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 1.76/0.99      inference(renaming,[status(thm)],[c_732]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1096,plain,
% 1.76/0.99      ( k1_relset_1(sK3,sK4,sK6) = sK3 ),
% 1.76/0.99      inference(equality_resolution_simp,[status(thm)],[c_733]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1485,plain,
% 1.76/0.99      ( k1_relset_1(sK3,sK4,sK6) = sK3 ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_1096]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2306,plain,
% 1.76/0.99      ( k1_relat_1(sK6) = sK3 ),
% 1.76/0.99      inference(light_normalisation,[status(thm)],[c_2193,c_1485]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2486,plain,
% 1.76/0.99      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0_51)) = X0_51
% 1.76/0.99      | r2_hidden(X0_51,sK3) != iProver_top ),
% 1.76/0.99      inference(light_normalisation,[status(thm)],[c_2481,c_2306]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_2490,plain,
% 1.76/0.99      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) = sK5
% 1.76/0.99      | r2_hidden(sK5,sK3) != iProver_top ),
% 1.76/0.99      inference(instantiation,[status(thm)],[c_2486]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_23,negated_conjecture,
% 1.76/0.99      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5 ),
% 1.76/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_1500,negated_conjecture,
% 1.76/0.99      ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK5)) != sK5 ),
% 1.76/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_25,negated_conjecture,
% 1.76/0.99      ( r2_hidden(sK5,sK3) ),
% 1.76/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(c_34,plain,
% 1.76/0.99      ( r2_hidden(sK5,sK3) = iProver_top ),
% 1.76/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.76/0.99  
% 1.76/0.99  cnf(contradiction,plain,
% 1.76/0.99      ( $false ),
% 1.76/0.99      inference(minisat,[status(thm)],[c_2490,c_1500,c_34]) ).
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.76/0.99  
% 1.76/0.99  ------                               Statistics
% 1.76/0.99  
% 1.76/0.99  ------ General
% 1.76/0.99  
% 1.76/0.99  abstr_ref_over_cycles:                  0
% 1.76/0.99  abstr_ref_under_cycles:                 0
% 1.76/0.99  gc_basic_clause_elim:                   0
% 1.76/0.99  forced_gc_time:                         0
% 1.76/0.99  parsing_time:                           0.011
% 1.76/0.99  unif_index_cands_time:                  0.
% 1.76/0.99  unif_index_add_time:                    0.
% 1.76/0.99  orderings_time:                         0.
% 1.76/0.99  out_proof_time:                         0.007
% 1.76/0.99  total_time:                             0.118
% 1.76/0.99  num_of_symbols:                         58
% 1.76/0.99  num_of_terms:                           2139
% 1.76/0.99  
% 1.76/0.99  ------ Preprocessing
% 1.76/0.99  
% 1.76/0.99  num_of_splits:                          3
% 1.76/0.99  num_of_split_atoms:                     3
% 1.76/0.99  num_of_reused_defs:                     0
% 1.76/0.99  num_eq_ax_congr_red:                    12
% 1.76/0.99  num_of_sem_filtered_clauses:            1
% 1.76/0.99  num_of_subtypes:                        3
% 1.76/0.99  monotx_restored_types:                  1
% 1.76/0.99  sat_num_of_epr_types:                   0
% 1.76/0.99  sat_num_of_non_cyclic_types:            0
% 1.76/0.99  sat_guarded_non_collapsed_types:        1
% 1.76/0.99  num_pure_diseq_elim:                    0
% 1.76/0.99  simp_replaced_by:                       0
% 1.76/0.99  res_preprocessed:                       147
% 1.76/0.99  prep_upred:                             0
% 1.76/0.99  prep_unflattend:                        175
% 1.76/0.99  smt_new_axioms:                         0
% 1.76/0.99  pred_elim_cands:                        4
% 1.76/0.99  pred_elim:                              3
% 1.76/0.99  pred_elim_cl:                           6
% 1.76/0.99  pred_elim_cycles:                       5
% 1.76/0.99  merged_defs:                            0
% 1.76/0.99  merged_defs_ncl:                        0
% 1.76/0.99  bin_hyper_res:                          0
% 1.76/0.99  prep_cycles:                            4
% 1.76/0.99  pred_elim_time:                         0.024
% 1.76/0.99  splitting_time:                         0.
% 1.76/0.99  sem_filter_time:                        0.
% 1.76/0.99  monotx_time:                            0.001
% 1.76/0.99  subtype_inf_time:                       0.008
% 1.76/0.99  
% 1.76/0.99  ------ Problem properties
% 1.76/0.99  
% 1.76/0.99  clauses:                                27
% 1.76/0.99  conjectures:                            4
% 1.76/0.99  epr:                                    3
% 1.76/0.99  horn:                                   22
% 1.76/0.99  ground:                                 11
% 1.76/0.99  unary:                                  6
% 1.76/0.99  binary:                                 6
% 1.76/0.99  lits:                                   80
% 1.76/0.99  lits_eq:                                25
% 1.76/0.99  fd_pure:                                0
% 1.76/0.99  fd_pseudo:                              0
% 1.76/0.99  fd_cond:                                3
% 1.76/0.99  fd_pseudo_cond:                         1
% 1.76/0.99  ac_symbols:                             0
% 1.76/0.99  
% 1.76/0.99  ------ Propositional Solver
% 1.76/0.99  
% 1.76/0.99  prop_solver_calls:                      25
% 1.76/0.99  prop_fast_solver_calls:                 1168
% 1.76/0.99  smt_solver_calls:                       0
% 1.76/0.99  smt_fast_solver_calls:                  0
% 1.76/0.99  prop_num_of_clauses:                    499
% 1.76/0.99  prop_preprocess_simplified:             3694
% 1.76/0.99  prop_fo_subsumed:                       19
% 1.76/0.99  prop_solver_time:                       0.
% 1.76/0.99  smt_solver_time:                        0.
% 1.76/0.99  smt_fast_solver_time:                   0.
% 1.76/0.99  prop_fast_solver_time:                  0.
% 1.76/0.99  prop_unsat_core_time:                   0.
% 1.76/0.99  
% 1.76/0.99  ------ QBF
% 1.76/0.99  
% 1.76/0.99  qbf_q_res:                              0
% 1.76/0.99  qbf_num_tautologies:                    0
% 1.76/0.99  qbf_prep_cycles:                        0
% 1.76/0.99  
% 1.76/0.99  ------ BMC1
% 1.76/0.99  
% 1.76/0.99  bmc1_current_bound:                     -1
% 1.76/0.99  bmc1_last_solved_bound:                 -1
% 1.76/0.99  bmc1_unsat_core_size:                   -1
% 1.76/0.99  bmc1_unsat_core_parents_size:           -1
% 1.76/0.99  bmc1_merge_next_fun:                    0
% 1.76/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.76/0.99  
% 1.76/0.99  ------ Instantiation
% 1.76/0.99  
% 1.76/0.99  inst_num_of_clauses:                    128
% 1.76/0.99  inst_num_in_passive:                    29
% 1.76/0.99  inst_num_in_active:                     97
% 1.76/0.99  inst_num_in_unprocessed:                2
% 1.76/0.99  inst_num_of_loops:                      100
% 1.76/0.99  inst_num_of_learning_restarts:          0
% 1.76/0.99  inst_num_moves_active_passive:          0
% 1.76/0.99  inst_lit_activity:                      0
% 1.76/0.99  inst_lit_activity_moves:                0
% 1.76/0.99  inst_num_tautologies:                   0
% 1.76/0.99  inst_num_prop_implied:                  0
% 1.76/0.99  inst_num_existing_simplified:           0
% 1.76/0.99  inst_num_eq_res_simplified:             0
% 1.76/0.99  inst_num_child_elim:                    0
% 1.76/0.99  inst_num_of_dismatching_blockings:      6
% 1.76/0.99  inst_num_of_non_proper_insts:           83
% 1.76/0.99  inst_num_of_duplicates:                 0
% 1.76/0.99  inst_inst_num_from_inst_to_res:         0
% 1.76/0.99  inst_dismatching_checking_time:         0.
% 1.76/0.99  
% 1.76/0.99  ------ Resolution
% 1.76/0.99  
% 1.76/0.99  res_num_of_clauses:                     0
% 1.76/0.99  res_num_in_passive:                     0
% 1.76/0.99  res_num_in_active:                      0
% 1.76/0.99  res_num_of_loops:                       151
% 1.76/0.99  res_forward_subset_subsumed:            18
% 1.76/0.99  res_backward_subset_subsumed:           0
% 1.76/0.99  res_forward_subsumed:                   0
% 1.76/0.99  res_backward_subsumed:                  0
% 1.76/0.99  res_forward_subsumption_resolution:     0
% 1.76/0.99  res_backward_subsumption_resolution:    0
% 1.76/0.99  res_clause_to_clause_subsumption:       81
% 1.76/0.99  res_orphan_elimination:                 0
% 1.76/0.99  res_tautology_del:                      43
% 1.76/0.99  res_num_eq_res_simplified:              1
% 1.76/0.99  res_num_sel_changes:                    0
% 1.76/0.99  res_moves_from_active_to_pass:          0
% 1.76/0.99  
% 1.76/0.99  ------ Superposition
% 1.76/0.99  
% 1.76/0.99  sup_time_total:                         0.
% 1.76/0.99  sup_time_generating:                    0.
% 1.76/0.99  sup_time_sim_full:                      0.
% 1.76/0.99  sup_time_sim_immed:                     0.
% 1.76/0.99  
% 1.76/0.99  sup_num_of_clauses:                     27
% 1.76/0.99  sup_num_in_active:                      18
% 1.76/0.99  sup_num_in_passive:                     9
% 1.76/0.99  sup_num_of_loops:                       19
% 1.76/0.99  sup_fw_superposition:                   0
% 1.76/0.99  sup_bw_superposition:                   0
% 1.76/0.99  sup_immediate_simplified:               0
% 1.76/0.99  sup_given_eliminated:                   0
% 1.76/0.99  comparisons_done:                       0
% 1.76/0.99  comparisons_avoided:                    0
% 1.76/0.99  
% 1.76/0.99  ------ Simplifications
% 1.76/0.99  
% 1.76/0.99  
% 1.76/0.99  sim_fw_subset_subsumed:                 0
% 1.76/0.99  sim_bw_subset_subsumed:                 0
% 1.76/0.99  sim_fw_subsumed:                        0
% 1.76/0.99  sim_bw_subsumed:                        0
% 1.76/0.99  sim_fw_subsumption_res:                 0
% 1.76/0.99  sim_bw_subsumption_res:                 0
% 1.76/0.99  sim_tautology_del:                      0
% 1.76/0.99  sim_eq_tautology_del:                   0
% 1.76/0.99  sim_eq_res_simp:                        0
% 1.76/0.99  sim_fw_demodulated:                     0
% 1.76/0.99  sim_bw_demodulated:                     1
% 1.76/0.99  sim_light_normalised:                   3
% 1.76/0.99  sim_joinable_taut:                      0
% 1.76/0.99  sim_joinable_simp:                      0
% 1.76/0.99  sim_ac_normalised:                      0
% 1.76/0.99  sim_smt_subsumption:                    0
% 1.76/0.99  
%------------------------------------------------------------------------------
