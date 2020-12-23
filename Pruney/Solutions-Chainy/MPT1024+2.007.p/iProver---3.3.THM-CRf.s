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
% DateTime   : Thu Dec  3 12:07:48 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  173 (3597 expanded)
%              Number of clauses        :  109 (1127 expanded)
%              Number of leaves         :   21 ( 913 expanded)
%              Depth                    :   32
%              Number of atoms          :  608 (20015 expanded)
%              Number of equality atoms :  291 (5264 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK1(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2)
                  & r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
                    & r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f28,f41,f40])).

fof(f72,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f70,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f74,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_850,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_837,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_840,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3098,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_840])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_847,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1472,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_837,c_847])).

cnf(c_3102,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3098,c_1472])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,plain,
    ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3322,plain,
    ( sK5 = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3102,c_33])).

cnf(c_3323,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3322])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_849,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4010,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3323,c_849])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1175,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1176,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_5216,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4010,c_32,c_34,c_1176])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_846,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2022,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_837,c_846])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_838,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2516,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2022,c_838])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_851,plain,
    ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4102,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_851])).

cnf(c_4834,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4102,c_32,c_34,c_1176])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_839,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4838,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4834,c_839])).

cnf(c_5227,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5216,c_4838])).

cnf(c_5243,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5227,c_2516])).

cnf(c_5244,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_5243])).

cnf(c_5249,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_5244])).

cnf(c_5417,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5249,c_32,c_34,c_1176,c_2516])).

cnf(c_5423,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5417,c_837])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_844,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6073,plain,
    ( sK4 = k1_xboole_0
    | sK7 = k1_xboole_0
    | v1_funct_2(sK7,sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5423,c_844])).

cnf(c_297,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_326,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_1419,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_311,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1294,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X2 != sK5
    | X1 != sK4
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_1418,plain,
    ( v1_funct_2(sK7,X0,X1)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X1 != sK5
    | X0 != sK4
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_1744,plain,
    ( v1_funct_2(sK7,sK4,X0)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X0 != sK5
    | sK4 != sK4
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1418])).

cnf(c_1746,plain,
    ( X0 != sK5
    | sK4 != sK4
    | sK7 != sK7
    | v1_funct_2(sK7,sK4,X0) = iProver_top
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1744])).

cnf(c_1748,plain,
    ( sK4 != sK4
    | sK7 != sK7
    | k1_xboole_0 != sK5
    | v1_funct_2(sK7,sK4,sK5) != iProver_top
    | v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_1745,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_298,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2493,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_2494,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2493])).

cnf(c_6235,plain,
    ( sK7 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6073,c_32,c_33,c_34,c_326,c_1176,c_1419,c_1748,c_1745,c_2494,c_2516,c_5249])).

cnf(c_6236,plain,
    ( sK4 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6235])).

cnf(c_5421,plain,
    ( k7_relset_1(sK4,k1_xboole_0,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(demodulation,[status(thm)],[c_5417,c_2022])).

cnf(c_6360,plain,
    ( k7_relset_1(k1_xboole_0,k1_xboole_0,sK7,X0) = k9_relat_1(sK7,X0)
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6236,c_5421])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_114,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_115,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_300,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_6434,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK7),X1)
    | k1_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_6435,plain,
    ( k1_relat_1(sK7) != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK7),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6434])).

cnf(c_6437,plain,
    ( k1_relat_1(sK7) != k1_xboole_0
    | r1_tarski(k1_relat_1(sK7),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6435])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_857,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_864,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_863,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2209,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_864,c_863])).

cnf(c_2657,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_2209])).

cnf(c_6834,plain,
    ( r1_tarski(k1_relat_1(sK7),X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_2657])).

cnf(c_6954,plain,
    ( r1_tarski(k1_relat_1(sK7),k1_xboole_0) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6834])).

cnf(c_5422,plain,
    ( k1_relset_1(sK4,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
    inference(demodulation,[status(thm)],[c_5417,c_1472])).

cnf(c_6260,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_relat_1(sK7)
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6236,c_5422])).

cnf(c_6239,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6236,c_5423])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_841,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6614,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
    | sK7 = k1_xboole_0
    | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6239,c_841])).

cnf(c_836,plain,
    ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5424,plain,
    ( v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5417,c_836])).

cnf(c_6240,plain,
    ( sK7 = k1_xboole_0
    | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6236,c_5424])).

cnf(c_7113,plain,
    ( sK7 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6614,c_6240])).

cnf(c_7114,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7113])).

cnf(c_7508,plain,
    ( k1_relat_1(sK7) = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6260,c_7114])).

cnf(c_7690,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6360,c_34,c_114,c_115,c_1176,c_6437,c_6954,c_7508])).

cnf(c_7708,plain,
    ( r2_hidden(sK8,k9_relat_1(k1_xboole_0,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7690,c_2516])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_858,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2948,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_2209])).

cnf(c_8072,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7708,c_2948])).

cnf(c_8189,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8072])).

cnf(c_1369,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1370,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_1372,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_1350,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_2,c_18])).

cnf(c_1351,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1350])).

cnf(c_1353,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8189,c_1372,c_1353,c_115,c_114])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.37/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.37/1.04  
% 0.37/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.37/1.04  
% 0.37/1.04  ------  iProver source info
% 0.37/1.04  
% 0.37/1.04  git: date: 2020-06-30 10:37:57 +0100
% 0.37/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.37/1.04  git: non_committed_changes: false
% 0.37/1.04  git: last_make_outside_of_git: false
% 0.37/1.04  
% 0.37/1.04  ------ 
% 0.37/1.04  ------ Parsing...
% 0.37/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.37/1.04  
% 0.37/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.37/1.04  ------ Proving...
% 0.37/1.04  ------ Problem Properties 
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  clauses                                 32
% 0.37/1.04  conjectures                             5
% 0.37/1.04  EPR                                     4
% 0.37/1.04  Horn                                    25
% 0.37/1.04  unary                                   7
% 0.37/1.04  binary                                  4
% 0.37/1.04  lits                                    98
% 0.37/1.04  lits eq                                 19
% 0.37/1.04  fd_pure                                 0
% 0.37/1.04  fd_pseudo                               0
% 0.37/1.04  fd_cond                                 3
% 0.37/1.04  fd_pseudo_cond                          4
% 0.37/1.04  AC symbols                              0
% 0.37/1.04  
% 0.37/1.04  ------ Input Options Time Limit: Unbounded
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  ------ 
% 0.37/1.04  Current options:
% 0.37/1.04  ------ 
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  ------ Proving...
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  % SZS status Theorem for theBenchmark.p
% 0.37/1.04  
% 0.37/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.37/1.04  
% 0.37/1.04  fof(f8,axiom,(
% 0.37/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f20,plain,(
% 0.37/1.04    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.37/1.04    inference(ennf_transformation,[],[f8])).
% 0.37/1.04  
% 0.37/1.04  fof(f21,plain,(
% 0.37/1.04    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.04    inference(flattening,[],[f20])).
% 0.37/1.04  
% 0.37/1.04  fof(f33,plain,(
% 0.37/1.04    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.04    inference(nnf_transformation,[],[f21])).
% 0.37/1.04  
% 0.37/1.04  fof(f34,plain,(
% 0.37/1.04    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.04    inference(rectify,[],[f33])).
% 0.37/1.04  
% 0.37/1.04  fof(f37,plain,(
% 0.37/1.04    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f36,plain,(
% 0.37/1.04    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f35,plain,(
% 0.37/1.04    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f38,plain,(
% 0.37/1.04    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.37/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f37,f36,f35])).
% 0.37/1.04  
% 0.37/1.04  fof(f54,plain,(
% 0.37/1.04    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f38])).
% 0.37/1.04  
% 0.37/1.04  fof(f78,plain,(
% 0.37/1.04    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.04    inference(equality_resolution,[],[f54])).
% 0.37/1.04  
% 0.37/1.04  fof(f13,conjecture,(
% 0.37/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f14,negated_conjecture,(
% 0.37/1.04    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.37/1.04    inference(negated_conjecture,[],[f13])).
% 0.37/1.04  
% 0.37/1.04  fof(f27,plain,(
% 0.37/1.04    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.37/1.04    inference(ennf_transformation,[],[f14])).
% 0.37/1.04  
% 0.37/1.04  fof(f28,plain,(
% 0.37/1.04    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.37/1.04    inference(flattening,[],[f27])).
% 0.37/1.04  
% 0.37/1.04  fof(f41,plain,(
% 0.37/1.04    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f40,plain,(
% 0.37/1.04    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f42,plain,(
% 0.37/1.04    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 0.37/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f28,f41,f40])).
% 0.37/1.04  
% 0.37/1.04  fof(f72,plain,(
% 0.37/1.04    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.37/1.04    inference(cnf_transformation,[],[f42])).
% 0.37/1.04  
% 0.37/1.04  fof(f12,axiom,(
% 0.37/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f25,plain,(
% 0.37/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.04    inference(ennf_transformation,[],[f12])).
% 0.37/1.04  
% 0.37/1.04  fof(f26,plain,(
% 0.37/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.04    inference(flattening,[],[f25])).
% 0.37/1.04  
% 0.37/1.04  fof(f39,plain,(
% 0.37/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.04    inference(nnf_transformation,[],[f26])).
% 0.37/1.04  
% 0.37/1.04  fof(f64,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f39])).
% 0.37/1.04  
% 0.37/1.04  fof(f10,axiom,(
% 0.37/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f23,plain,(
% 0.37/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.04    inference(ennf_transformation,[],[f10])).
% 0.37/1.04  
% 0.37/1.04  fof(f62,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f23])).
% 0.37/1.04  
% 0.37/1.04  fof(f71,plain,(
% 0.37/1.04    v1_funct_2(sK7,sK4,sK5)),
% 0.37/1.04    inference(cnf_transformation,[],[f42])).
% 0.37/1.04  
% 0.37/1.04  fof(f53,plain,(
% 0.37/1.04    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f38])).
% 0.37/1.04  
% 0.37/1.04  fof(f79,plain,(
% 0.37/1.04    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.04    inference(equality_resolution,[],[f53])).
% 0.37/1.04  
% 0.37/1.04  fof(f70,plain,(
% 0.37/1.04    v1_funct_1(sK7)),
% 0.37/1.04    inference(cnf_transformation,[],[f42])).
% 0.37/1.04  
% 0.37/1.04  fof(f9,axiom,(
% 0.37/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f22,plain,(
% 0.37/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.04    inference(ennf_transformation,[],[f9])).
% 0.37/1.04  
% 0.37/1.04  fof(f61,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f22])).
% 0.37/1.04  
% 0.37/1.04  fof(f11,axiom,(
% 0.37/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f24,plain,(
% 0.37/1.04    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.04    inference(ennf_transformation,[],[f11])).
% 0.37/1.04  
% 0.37/1.04  fof(f63,plain,(
% 0.37/1.04    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f24])).
% 0.37/1.04  
% 0.37/1.04  fof(f73,plain,(
% 0.37/1.04    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 0.37/1.04    inference(cnf_transformation,[],[f42])).
% 0.37/1.04  
% 0.37/1.04  fof(f55,plain,(
% 0.37/1.04    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f38])).
% 0.37/1.04  
% 0.37/1.04  fof(f77,plain,(
% 0.37/1.04    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.37/1.04    inference(equality_resolution,[],[f55])).
% 0.37/1.04  
% 0.37/1.04  fof(f74,plain,(
% 0.37/1.04    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f42])).
% 0.37/1.04  
% 0.37/1.04  fof(f68,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f39])).
% 0.37/1.04  
% 0.37/1.04  fof(f82,plain,(
% 0.37/1.04    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.37/1.04    inference(equality_resolution,[],[f68])).
% 0.37/1.04  
% 0.37/1.04  fof(f2,axiom,(
% 0.37/1.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f44,plain,(
% 0.37/1.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f2])).
% 0.37/1.04  
% 0.37/1.04  fof(f1,axiom,(
% 0.37/1.04    v1_xboole_0(k1_xboole_0)),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f43,plain,(
% 0.37/1.04    v1_xboole_0(k1_xboole_0)),
% 0.37/1.04    inference(cnf_transformation,[],[f1])).
% 0.37/1.04  
% 0.37/1.04  fof(f7,axiom,(
% 0.37/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f19,plain,(
% 0.37/1.04    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.37/1.04    inference(ennf_transformation,[],[f7])).
% 0.37/1.04  
% 0.37/1.04  fof(f29,plain,(
% 0.37/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.37/1.04    inference(nnf_transformation,[],[f19])).
% 0.37/1.04  
% 0.37/1.04  fof(f30,plain,(
% 0.37/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.37/1.04    inference(rectify,[],[f29])).
% 0.37/1.04  
% 0.37/1.04  fof(f31,plain,(
% 0.37/1.04    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 0.37/1.04    introduced(choice_axiom,[])).
% 0.37/1.04  
% 0.37/1.04  fof(f32,plain,(
% 0.37/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.37/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 0.37/1.04  
% 0.37/1.04  fof(f49,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f32])).
% 0.37/1.04  
% 0.37/1.04  fof(f3,axiom,(
% 0.37/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f15,plain,(
% 0.37/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.37/1.04    inference(unused_predicate_definition_removal,[],[f3])).
% 0.37/1.04  
% 0.37/1.04  fof(f16,plain,(
% 0.37/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.37/1.04    inference(ennf_transformation,[],[f15])).
% 0.37/1.04  
% 0.37/1.04  fof(f45,plain,(
% 0.37/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f16])).
% 0.37/1.04  
% 0.37/1.04  fof(f4,axiom,(
% 0.37/1.04    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.37/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.04  
% 0.37/1.04  fof(f17,plain,(
% 0.37/1.04    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.37/1.04    inference(ennf_transformation,[],[f4])).
% 0.37/1.04  
% 0.37/1.04  fof(f46,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f17])).
% 0.37/1.04  
% 0.37/1.04  fof(f65,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.04    inference(cnf_transformation,[],[f39])).
% 0.37/1.04  
% 0.37/1.04  fof(f84,plain,(
% 0.37/1.04    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.37/1.04    inference(equality_resolution,[],[f65])).
% 0.37/1.04  
% 0.37/1.04  fof(f50,plain,(
% 0.37/1.04    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.37/1.04    inference(cnf_transformation,[],[f32])).
% 0.37/1.04  
% 0.37/1.04  cnf(c_16,plain,
% 0.37/1.04      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 0.37/1.04      | r2_hidden(sK3(X1,X2,X0),X2)
% 0.37/1.04      | ~ v1_funct_1(X1)
% 0.37/1.04      | ~ v1_relat_1(X1) ),
% 0.37/1.04      inference(cnf_transformation,[],[f78]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_850,plain,
% 0.37/1.04      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 0.37/1.04      | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
% 0.37/1.04      | v1_funct_1(X1) != iProver_top
% 0.37/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_29,negated_conjecture,
% 0.37/1.04      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 0.37/1.04      inference(cnf_transformation,[],[f72]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_837,plain,
% 0.37/1.04      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_26,plain,
% 0.37/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.04      | k1_relset_1(X1,X2,X0) = X1
% 0.37/1.04      | k1_xboole_0 = X2 ),
% 0.37/1.04      inference(cnf_transformation,[],[f64]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_840,plain,
% 0.37/1.04      ( k1_relset_1(X0,X1,X2) = X0
% 0.37/1.04      | k1_xboole_0 = X1
% 0.37/1.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 0.37/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3098,plain,
% 0.37/1.04      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 0.37/1.04      | sK5 = k1_xboole_0
% 0.37/1.04      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_837,c_840]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_19,plain,
% 0.37/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 0.37/1.04      inference(cnf_transformation,[],[f62]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_847,plain,
% 0.37/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 0.37/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1472,plain,
% 0.37/1.04      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_837,c_847]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3102,plain,
% 0.37/1.04      ( k1_relat_1(sK7) = sK4
% 0.37/1.04      | sK5 = k1_xboole_0
% 0.37/1.04      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_3098,c_1472]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_30,negated_conjecture,
% 0.37/1.04      ( v1_funct_2(sK7,sK4,sK5) ),
% 0.37/1.04      inference(cnf_transformation,[],[f71]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_33,plain,
% 0.37/1.04      ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3322,plain,
% 0.37/1.04      ( sK5 = k1_xboole_0 | k1_relat_1(sK7) = sK4 ),
% 0.37/1.04      inference(global_propositional_subsumption,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_3102,c_33]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3323,plain,
% 0.37/1.04      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 0.37/1.04      inference(renaming,[status(thm)],[c_3322]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_17,plain,
% 0.37/1.04      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 0.37/1.04      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 0.37/1.04      | ~ v1_funct_1(X1)
% 0.37/1.04      | ~ v1_relat_1(X1) ),
% 0.37/1.04      inference(cnf_transformation,[],[f79]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_849,plain,
% 0.37/1.04      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 0.37/1.04      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 0.37/1.04      | v1_funct_1(X1) != iProver_top
% 0.37/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_4010,plain,
% 0.37/1.04      ( sK5 = k1_xboole_0
% 0.37/1.04      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 0.37/1.04      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
% 0.37/1.04      | v1_funct_1(sK7) != iProver_top
% 0.37/1.04      | v1_relat_1(sK7) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_3323,c_849]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_31,negated_conjecture,
% 0.37/1.04      ( v1_funct_1(sK7) ),
% 0.37/1.04      inference(cnf_transformation,[],[f70]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_32,plain,
% 0.37/1.04      ( v1_funct_1(sK7) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_34,plain,
% 0.37/1.04      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_18,plain,
% 0.37/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.04      | v1_relat_1(X0) ),
% 0.37/1.04      inference(cnf_transformation,[],[f61]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1175,plain,
% 0.37/1.04      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 0.37/1.04      | v1_relat_1(sK7) ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_18]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1176,plain,
% 0.37/1.04      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 0.37/1.04      | v1_relat_1(sK7) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5216,plain,
% 0.37/1.04      ( sK5 = k1_xboole_0
% 0.37/1.04      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 0.37/1.04      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
% 0.37/1.04      inference(global_propositional_subsumption,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_4010,c_32,c_34,c_1176]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_20,plain,
% 0.37/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.04      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 0.37/1.04      inference(cnf_transformation,[],[f63]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_846,plain,
% 0.37/1.04      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 0.37/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2022,plain,
% 0.37/1.04      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_837,c_846]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_28,negated_conjecture,
% 0.37/1.04      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 0.37/1.04      inference(cnf_transformation,[],[f73]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_838,plain,
% 0.37/1.04      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2516,plain,
% 0.37/1.04      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_2022,c_838]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_15,plain,
% 0.37/1.04      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 0.37/1.04      | ~ v1_funct_1(X1)
% 0.37/1.04      | ~ v1_relat_1(X1)
% 0.37/1.04      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 0.37/1.04      inference(cnf_transformation,[],[f77]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_851,plain,
% 0.37/1.04      ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
% 0.37/1.04      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 0.37/1.04      | v1_funct_1(X0) != iProver_top
% 0.37/1.04      | v1_relat_1(X0) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_4102,plain,
% 0.37/1.04      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
% 0.37/1.04      | v1_funct_1(sK7) != iProver_top
% 0.37/1.04      | v1_relat_1(sK7) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_2516,c_851]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_4834,plain,
% 0.37/1.04      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
% 0.37/1.04      inference(global_propositional_subsumption,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_4102,c_32,c_34,c_1176]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_27,negated_conjecture,
% 0.37/1.04      ( ~ r2_hidden(X0,sK4)
% 0.37/1.04      | ~ r2_hidden(X0,sK6)
% 0.37/1.04      | k1_funct_1(sK7,X0) != sK8 ),
% 0.37/1.04      inference(cnf_transformation,[],[f74]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_839,plain,
% 0.37/1.04      ( k1_funct_1(sK7,X0) != sK8
% 0.37/1.04      | r2_hidden(X0,sK4) != iProver_top
% 0.37/1.04      | r2_hidden(X0,sK6) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_4838,plain,
% 0.37/1.04      ( r2_hidden(sK3(sK7,sK6,sK8),sK4) != iProver_top
% 0.37/1.04      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_4834,c_839]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5227,plain,
% 0.37/1.04      ( sK5 = k1_xboole_0
% 0.37/1.04      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 0.37/1.04      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_5216,c_4838]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5243,plain,
% 0.37/1.04      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 0.37/1.04      | sK5 = k1_xboole_0 ),
% 0.37/1.04      inference(global_propositional_subsumption,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_5227,c_2516]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5244,plain,
% 0.37/1.04      ( sK5 = k1_xboole_0
% 0.37/1.04      | r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top ),
% 0.37/1.04      inference(renaming,[status(thm)],[c_5243]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5249,plain,
% 0.37/1.04      ( sK5 = k1_xboole_0
% 0.37/1.04      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 0.37/1.04      | v1_funct_1(sK7) != iProver_top
% 0.37/1.04      | v1_relat_1(sK7) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_850,c_5244]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5417,plain,
% 0.37/1.04      ( sK5 = k1_xboole_0 ),
% 0.37/1.04      inference(global_propositional_subsumption,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_5249,c_32,c_34,c_1176,c_2516]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5423,plain,
% 0.37/1.04      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_5417,c_837]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_22,plain,
% 0.37/1.04      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 0.37/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 0.37/1.04      | k1_xboole_0 = X1
% 0.37/1.04      | k1_xboole_0 = X0 ),
% 0.37/1.04      inference(cnf_transformation,[],[f82]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_844,plain,
% 0.37/1.04      ( k1_xboole_0 = X0
% 0.37/1.04      | k1_xboole_0 = X1
% 0.37/1.04      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 0.37/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6073,plain,
% 0.37/1.04      ( sK4 = k1_xboole_0
% 0.37/1.04      | sK7 = k1_xboole_0
% 0.37/1.04      | v1_funct_2(sK7,sK4,k1_xboole_0) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_5423,c_844]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_297,plain,( X0 = X0 ),theory(equality) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_326,plain,
% 0.37/1.04      ( k1_xboole_0 = k1_xboole_0 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_297]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1419,plain,
% 0.37/1.04      ( sK7 = sK7 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_297]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_311,plain,
% 0.37/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 0.37/1.04      | v1_funct_2(X3,X4,X5)
% 0.37/1.04      | X3 != X0
% 0.37/1.04      | X4 != X1
% 0.37/1.04      | X5 != X2 ),
% 0.37/1.04      theory(equality) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1294,plain,
% 0.37/1.04      ( v1_funct_2(X0,X1,X2)
% 0.37/1.04      | ~ v1_funct_2(sK7,sK4,sK5)
% 0.37/1.04      | X2 != sK5
% 0.37/1.04      | X1 != sK4
% 0.37/1.04      | X0 != sK7 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_311]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1418,plain,
% 0.37/1.04      ( v1_funct_2(sK7,X0,X1)
% 0.37/1.04      | ~ v1_funct_2(sK7,sK4,sK5)
% 0.37/1.04      | X1 != sK5
% 0.37/1.04      | X0 != sK4
% 0.37/1.04      | sK7 != sK7 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1294]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1744,plain,
% 0.37/1.04      ( v1_funct_2(sK7,sK4,X0)
% 0.37/1.04      | ~ v1_funct_2(sK7,sK4,sK5)
% 0.37/1.04      | X0 != sK5
% 0.37/1.04      | sK4 != sK4
% 0.37/1.04      | sK7 != sK7 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1418]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1746,plain,
% 0.37/1.04      ( X0 != sK5
% 0.37/1.04      | sK4 != sK4
% 0.37/1.04      | sK7 != sK7
% 0.37/1.04      | v1_funct_2(sK7,sK4,X0) = iProver_top
% 0.37/1.04      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_1744]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1748,plain,
% 0.37/1.04      ( sK4 != sK4
% 0.37/1.04      | sK7 != sK7
% 0.37/1.04      | k1_xboole_0 != sK5
% 0.37/1.04      | v1_funct_2(sK7,sK4,sK5) != iProver_top
% 0.37/1.04      | v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1746]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1745,plain,
% 0.37/1.04      ( sK4 = sK4 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_297]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_298,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2493,plain,
% 0.37/1.04      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_298]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2494,plain,
% 0.37/1.04      ( sK5 != k1_xboole_0
% 0.37/1.04      | k1_xboole_0 = sK5
% 0.37/1.04      | k1_xboole_0 != k1_xboole_0 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_2493]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6235,plain,
% 0.37/1.04      ( sK7 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 0.37/1.04      inference(global_propositional_subsumption,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_6073,c_32,c_33,c_34,c_326,c_1176,c_1419,c_1748,c_1745,
% 0.37/1.04                 c_2494,c_2516,c_5249]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6236,plain,
% 0.37/1.04      ( sK4 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 0.37/1.04      inference(renaming,[status(thm)],[c_6235]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5421,plain,
% 0.37/1.04      ( k7_relset_1(sK4,k1_xboole_0,sK7,X0) = k9_relat_1(sK7,X0) ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_5417,c_2022]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6360,plain,
% 0.37/1.04      ( k7_relset_1(k1_xboole_0,k1_xboole_0,sK7,X0) = k9_relat_1(sK7,X0)
% 0.37/1.04      | sK7 = k1_xboole_0 ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_6236,c_5421]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,X0) ),
% 0.37/1.04      inference(cnf_transformation,[],[f44]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_112,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_114,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_112]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_0,plain,
% 0.37/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 0.37/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_115,plain,
% 0.37/1.04      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_300,plain,
% 0.37/1.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 0.37/1.04      theory(equality) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6434,plain,
% 0.37/1.04      ( ~ r1_tarski(X0,X1)
% 0.37/1.04      | r1_tarski(k1_relat_1(sK7),X1)
% 0.37/1.04      | k1_relat_1(sK7) != X0 ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_300]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6435,plain,
% 0.37/1.04      ( k1_relat_1(sK7) != X0
% 0.37/1.04      | r1_tarski(X0,X1) != iProver_top
% 0.37/1.04      | r1_tarski(k1_relat_1(sK7),X1) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_6434]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6437,plain,
% 0.37/1.04      ( k1_relat_1(sK7) != k1_xboole_0
% 0.37/1.04      | r1_tarski(k1_relat_1(sK7),k1_xboole_0) = iProver_top
% 0.37/1.04      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_6435]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_9,plain,
% 0.37/1.04      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 0.37/1.04      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 0.37/1.04      | ~ v1_relat_1(X1) ),
% 0.37/1.04      inference(cnf_transformation,[],[f49]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_857,plain,
% 0.37/1.04      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 0.37/1.04      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 0.37/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2,plain,
% 0.37/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.37/1.04      inference(cnf_transformation,[],[f45]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_864,plain,
% 0.37/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 0.37/1.04      | r1_tarski(X0,X1) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_3,plain,
% 0.37/1.04      ( ~ r2_hidden(X0,X1)
% 0.37/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 0.37/1.04      | ~ v1_xboole_0(X2) ),
% 0.37/1.04      inference(cnf_transformation,[],[f46]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_863,plain,
% 0.37/1.04      ( r2_hidden(X0,X1) != iProver_top
% 0.37/1.04      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 0.37/1.04      | v1_xboole_0(X2) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2209,plain,
% 0.37/1.04      ( r2_hidden(X0,X1) != iProver_top
% 0.37/1.04      | r1_tarski(X1,X2) != iProver_top
% 0.37/1.04      | v1_xboole_0(X2) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_864,c_863]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2657,plain,
% 0.37/1.04      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 0.37/1.04      | r1_tarski(k1_relat_1(X1),X3) != iProver_top
% 0.37/1.04      | v1_relat_1(X1) != iProver_top
% 0.37/1.04      | v1_xboole_0(X3) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_857,c_2209]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6834,plain,
% 0.37/1.04      ( r1_tarski(k1_relat_1(sK7),X0) != iProver_top
% 0.37/1.04      | v1_relat_1(sK7) != iProver_top
% 0.37/1.04      | v1_xboole_0(X0) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_2516,c_2657]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6954,plain,
% 0.37/1.04      ( r1_tarski(k1_relat_1(sK7),k1_xboole_0) != iProver_top
% 0.37/1.04      | v1_relat_1(sK7) != iProver_top
% 0.37/1.04      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_6834]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5422,plain,
% 0.37/1.04      ( k1_relset_1(sK4,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_5417,c_1472]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6260,plain,
% 0.37/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_relat_1(sK7)
% 0.37/1.04      | sK7 = k1_xboole_0 ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_6236,c_5422]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6239,plain,
% 0.37/1.04      ( sK7 = k1_xboole_0
% 0.37/1.04      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_6236,c_5423]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_25,plain,
% 0.37/1.04      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 0.37/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 0.37/1.04      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 0.37/1.04      inference(cnf_transformation,[],[f84]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_841,plain,
% 0.37/1.04      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 0.37/1.04      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 0.37/1.04      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6614,plain,
% 0.37/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
% 0.37/1.04      | sK7 = k1_xboole_0
% 0.37/1.04      | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_6239,c_841]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_836,plain,
% 0.37/1.04      ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_5424,plain,
% 0.37/1.04      ( v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_5417,c_836]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_6240,plain,
% 0.37/1.04      ( sK7 = k1_xboole_0
% 0.37/1.04      | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_6236,c_5424]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_7113,plain,
% 0.37/1.04      ( sK7 = k1_xboole_0
% 0.37/1.04      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0 ),
% 0.37/1.04      inference(global_propositional_subsumption,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_6614,c_6240]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_7114,plain,
% 0.37/1.04      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
% 0.37/1.04      | sK7 = k1_xboole_0 ),
% 0.37/1.04      inference(renaming,[status(thm)],[c_7113]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_7508,plain,
% 0.37/1.04      ( k1_relat_1(sK7) = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_6260,c_7114]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_7690,plain,
% 0.37/1.04      ( sK7 = k1_xboole_0 ),
% 0.37/1.04      inference(global_propositional_subsumption,
% 0.37/1.04                [status(thm)],
% 0.37/1.04                [c_6360,c_34,c_114,c_115,c_1176,c_6437,c_6954,c_7508]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_7708,plain,
% 0.37/1.04      ( r2_hidden(sK8,k9_relat_1(k1_xboole_0,sK6)) = iProver_top ),
% 0.37/1.04      inference(demodulation,[status(thm)],[c_7690,c_2516]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_8,plain,
% 0.37/1.04      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 0.37/1.04      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 0.37/1.04      | ~ v1_relat_1(X1) ),
% 0.37/1.04      inference(cnf_transformation,[],[f50]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_858,plain,
% 0.37/1.04      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 0.37/1.04      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 0.37/1.04      | v1_relat_1(X1) != iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_2948,plain,
% 0.37/1.04      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 0.37/1.04      | r1_tarski(X1,X3) != iProver_top
% 0.37/1.04      | v1_relat_1(X1) != iProver_top
% 0.37/1.04      | v1_xboole_0(X3) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_858,c_2209]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_8072,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 0.37/1.04      | v1_relat_1(k1_xboole_0) != iProver_top
% 0.37/1.04      | v1_xboole_0(X0) != iProver_top ),
% 0.37/1.04      inference(superposition,[status(thm)],[c_7708,c_2948]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_8189,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 0.37/1.04      | v1_relat_1(k1_xboole_0) != iProver_top
% 0.37/1.04      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_8072]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1369,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1370,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1372,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1370]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1350,plain,
% 0.37/1.04      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0) ),
% 0.37/1.04      inference(resolution,[status(thm)],[c_2,c_18]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1351,plain,
% 0.37/1.04      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 0.37/1.04      | v1_relat_1(X0) = iProver_top ),
% 0.37/1.04      inference(predicate_to_equality,[status(thm)],[c_1350]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(c_1353,plain,
% 0.37/1.04      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 0.37/1.04      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 0.37/1.04      inference(instantiation,[status(thm)],[c_1351]) ).
% 0.37/1.04  
% 0.37/1.04  cnf(contradiction,plain,
% 0.37/1.04      ( $false ),
% 0.37/1.04      inference(minisat,[status(thm)],[c_8189,c_1372,c_1353,c_115,c_114]) ).
% 0.37/1.04  
% 0.37/1.04  
% 0.37/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.37/1.04  
% 0.37/1.04  ------                               Statistics
% 0.37/1.04  
% 0.37/1.04  ------ Selected
% 0.37/1.04  
% 0.37/1.04  total_time:                             0.361
% 0.37/1.04  
%------------------------------------------------------------------------------
