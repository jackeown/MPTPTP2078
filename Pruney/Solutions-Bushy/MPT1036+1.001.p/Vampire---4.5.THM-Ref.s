%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1036+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 (7032 expanded)
%              Number of leaves         :    6 (2088 expanded)
%              Depth                    :   37
%              Number of atoms          :  482 (67862 expanded)
%              Number of equality atoms :  121 (13629 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(global_subsumption,[],[f102,f108,f112])).

fof(f112,plain,(
    k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f19,f21,f78,f77,f79,f108,f33])).

fof(f33,plain,(
    ! [X2,X3,X1] :
      ( k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3))
      | r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ( k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
                & r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
        & r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f23,f76])).

fof(f76,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f75,f62])).

fof(f62,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f58,f26])).

fof(f26,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
        & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) )
      | ~ r1_partfun1(sK1,sK2) )
    & ( ! [X4] :
          ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
          | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
      | r1_partfun1(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                  & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
              | ~ r1_partfun1(X1,X2) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X1,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
              | r1_partfun1(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
                & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
            | ~ r1_partfun1(sK1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(sK1,X4)
                | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
            | r1_partfun1(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
              & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
          | ~ r1_partfun1(sK1,X2) )
        & ( ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(sK1,X4)
              | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
          | r1_partfun1(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ( ? [X3] :
            ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
            & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
        | ~ r1_partfun1(sK1,sK2) )
      & ( ! [X4] :
            ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1)) )
        | r1_partfun1(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
        & r2_hidden(X3,k1_relset_1(sK0,sK0,sK1)) )
   => ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
      & r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X1,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
                & r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | ~ r1_partfun1(X1,X2) )
          & ( ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) )
            | r1_partfun1(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f56,f25])).

fof(f25,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relset_1(sK0,sK0,sK1))
      | k1_xboole_0 = sK0
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f55,f24])).

fof(f24,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relset_1(sK0,sK0,sK1))
      | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | r1_partfun1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,k1_relset_1(sK0,sK0,sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_partfun1(sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f53,f19])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ r2_hidden(X0,k1_relset_1(sK0,sK0,sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_partfun1(sK1,sK2)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f52,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X1,k1_relset_1(sK0,sK0,X0))
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ r1_partfun1(X0,sK2)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f51,f22])).

fof(f22,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_partfun1(X0,sK2)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X1,k1_relset_1(sK0,sK0,X0))
      | ~ v1_funct_2(sK2,sK0,sK0)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f38,f23])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_partfun1(X3,sK2)
      | k1_xboole_0 = X2
      | ~ r2_hidden(X0,k1_relset_1(X1,X2,X3))
      | ~ v1_funct_2(sK2,X1,X2)
      | k1_funct_1(sK2,X0) = k1_funct_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f74,f19])).

fof(f74,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f73,f20])).

fof(f73,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f72,f21])).

fof(f72,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f71,f22])).

fof(f71,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f70,f23])).

fof(f70,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) != k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) != k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2))
    | r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f31,f64])).

fof(f64,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f48,f21])).

fof(f48,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f46,f22])).

fof(f46,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,
    ( r1_partfun1(sK1,sK2)
    | r1_partfun1(sK1,sK2)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f43,f23])).

fof(f43,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | r1_partfun1(sK1,sK2)
      | r1_partfun1(sK1,X0)
      | k1_xboole_0 = sK0
      | k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f42,f19])).

fof(f42,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0))
      | r1_partfun1(sK1,sK2)
      | r1_partfun1(sK1,X0)
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f40,f20])).

fof(f40,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0))
      | r1_partfun1(sK1,sK2)
      | r1_partfun1(sK1,X0)
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_2(X0,sK0,sK0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f24,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
      | r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f20,f76])).

fof(f78,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f22,f76])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f108,plain,(
    ~ r1_partfun1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f105,f26])).

fof(f105,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(resolution,[],[f96,f81])).

fof(f81,plain,
    ( r2_hidden(sK3,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(backward_demodulation,[],[f25,f76])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f95,f80])).

fof(f80,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
      | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
      | r1_partfun1(sK1,sK2) ) ),
    inference(backward_demodulation,[],[f24,f76])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_partfun1(sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f93,f19])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
      | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | ~ r1_partfun1(sK1,sK2)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f87,f77])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ r2_hidden(X1,k1_relset_1(k1_xboole_0,k1_xboole_0,X0))
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ r1_partfun1(X0,sK2)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f85,f78])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_partfun1(X0,sK2)
      | ~ r2_hidden(X1,k1_relset_1(k1_xboole_0,k1_xboole_0,X0))
      | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
      | k1_funct_1(X0,X1) = k1_funct_1(sK2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f79,f39])).

fof(f39,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ r1_partfun1(X6,sK2)
      | ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,X5,X6))
      | ~ v1_funct_2(sK2,k1_xboole_0,X5)
      | k1_funct_1(sK2,X4) = k1_funct_1(X6,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X6) ) ),
    inference(resolution,[],[f21,f35])).

fof(f35,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ r2_hidden(X5,k1_relset_1(k1_xboole_0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
      | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f101,f21])).

fof(f101,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f99,f78])).

fof(f99,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( r1_partfun1(sK1,sK2)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f92,f79])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | r1_partfun1(sK1,sK2)
      | r1_partfun1(sK1,X0)
      | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
      | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f91,f19])).

fof(f91,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
      | r1_partfun1(sK1,sK2)
      | r1_partfun1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f88,f77])).

fof(f88,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0))
      | r1_partfun1(sK1,sK2)
      | r1_partfun1(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f80,f34])).

fof(f34,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
      | r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
