%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:49 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  236 (5137 expanded)
%              Number of clauses        :  167 (1711 expanded)
%              Number of leaves         :   21 (1179 expanded)
%              Depth                    :   29
%              Number of atoms          :  756 (25447 expanded)
%              Number of equality atoms :  404 (6145 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f44,plain,(
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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f47,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ r2_hidden(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f27,f46,f45])).

fof(f76,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
        & r2_hidden(sK3(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
            & r2_hidden(sK3(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | k1_relset_1(X1,X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ r2_hidden(X5,sK4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK3(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2314,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_685,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X2
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_686,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_688,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_29])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k4_tarski(X3,sK2(X0,X3)),X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2303,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3846,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_688,c_2303])).

cnf(c_34,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2298,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2305,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3430,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2298,c_2305])).

cnf(c_3489,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_688,c_3430])).

cnf(c_3845,plain,
    ( k1_relat_1(sK7) != sK4
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3430,c_2303])).

cnf(c_3991,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3846,c_34,c_3489,c_3845])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2315,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3997,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),X1) = iProver_top
    | r1_tarski(sK7,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3991,c_2315])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2384,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2473,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2474,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2473])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2304,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3436,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_2298,c_2304])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2299,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3516,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3436,c_2299])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2309,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2307,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3775,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK7),sK4) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_2307])).

cnf(c_5311,plain,
    ( r2_hidden(sK1(X0,X1,sK7),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3775,c_34,c_2474])).

cnf(c_5312,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK7),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_5311])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2308,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_455,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_456,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_2294,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_457,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_2661,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | k1_funct_1(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2294,c_34,c_457,c_2474])).

cnf(c_2662,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_2661])).

cnf(c_3839,plain,
    ( k1_funct_1(sK7,sK1(X0,X1,sK7)) = X0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2308,c_2662])).

cnf(c_4014,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | k1_funct_1(sK7,sK1(X0,X1,sK7)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3839,c_34,c_2474])).

cnf(c_4015,plain,
    ( k1_funct_1(sK7,sK1(X0,X1,sK7)) = X0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4014])).

cnf(c_4024,plain,
    ( k1_funct_1(sK7,sK1(sK8,sK6,sK7)) = sK8 ),
    inference(superposition,[status(thm)],[c_3516,c_4015])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2300,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4100,plain,
    ( r2_hidden(sK1(sK8,sK6,sK7),sK4) != iProver_top
    | r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_2300])).

cnf(c_5319,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5312,c_4100])).

cnf(c_5534,plain,
    ( r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5319,c_3516])).

cnf(c_5535,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_5534])).

cnf(c_5538,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_5535])).

cnf(c_5541,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3997,c_34,c_2474,c_3516,c_5538])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK5 != k1_xboole_0
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_653,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK7 ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_2293,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_5548,plain,
    ( sK4 = k1_xboole_0
    | sK7 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5541,c_2293])).

cnf(c_5552,plain,
    ( sK4 = k1_xboole_0
    | sK7 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5548])).

cnf(c_654,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK7
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_1700,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3030,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3520,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_3521,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3520])).

cnf(c_1699,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3554,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2476,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK7,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3643,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
    | ~ r1_tarski(sK7,k2_zfmisc_1(sK4,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2476])).

cnf(c_3644,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3643])).

cnf(c_1701,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2865,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK7))
    | r1_tarski(X1,k1_relat_1(sK7))
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_4123,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK7))
    | r1_tarski(sK4,k1_relat_1(sK7))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2865])).

cnf(c_4125,plain,
    ( r1_tarski(sK4,k1_relat_1(sK7))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK7))
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4123])).

cnf(c_4440,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4447,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4448,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4447])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2312,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3016,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2298,c_2312])).

cnf(c_5547,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5541,c_3016])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2301,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3392,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | r2_hidden(sK3(sK4,sK7),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2298,c_2301])).

cnf(c_3544,plain,
    ( k1_relat_1(sK7) = sK4
    | r2_hidden(sK3(sK4,sK7),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3392,c_3430])).

cnf(c_3546,plain,
    ( k1_relat_1(sK7) = sK4
    | r2_hidden(sK3(sK4,sK7),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3544,c_2315])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_441,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_2295,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_442,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_2734,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2295,c_34,c_442,c_2474])).

cnf(c_2735,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_2734])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(sK3(X1,X0),X3),X0)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2302,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X2),X3),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3672,plain,
    ( k1_relset_1(X0,X1,sK7) = X0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,sK7),k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_2302])).

cnf(c_4469,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | r2_hidden(sK3(sK4,sK7),k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2298,c_3672])).

cnf(c_4470,plain,
    ( k1_relat_1(sK7) = sK4
    | r2_hidden(sK3(sK4,sK7),k1_relat_1(sK7)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4469,c_3430])).

cnf(c_5835,plain,
    ( k1_relat_1(sK7) = sK4
    | r1_tarski(sK4,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3546,c_4470])).

cnf(c_5840,plain,
    ( ~ r1_tarski(sK4,k1_relat_1(sK7))
    | k1_relat_1(sK7) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5835])).

cnf(c_2441,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(X1,sK4)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1701])).

cnf(c_3043,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k1_relat_1(X1),sK4)
    | k1_relat_1(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_6550,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k1_relat_1(sK7),sK4)
    | k1_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_3043])).

cnf(c_6553,plain,
    ( k1_relat_1(sK7) != X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6550])).

cnf(c_6555,plain,
    ( k1_relat_1(sK7) != k1_xboole_0
    | r1_tarski(k1_relat_1(sK7),sK4) = iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6553])).

cnf(c_2983,plain,
    ( X0 != X1
    | k1_relat_1(sK7) != X1
    | k1_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_6628,plain,
    ( X0 != sK4
    | k1_relat_1(sK7) = X0
    | k1_relat_1(sK7) != sK4 ),
    inference(instantiation,[status(thm)],[c_2983])).

cnf(c_6635,plain,
    ( k1_relat_1(sK7) != sK4
    | k1_relat_1(sK7) = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_6628])).

cnf(c_3776,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X3) = iProver_top
    | r1_tarski(k1_relat_1(X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_2315])).

cnf(c_7823,plain,
    ( r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3776,c_4100])).

cnf(c_8284,plain,
    ( r1_tarski(k1_relat_1(sK7),sK4) != iProver_top
    | r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7823,c_34,c_2474,c_3516])).

cnf(c_8285,plain,
    ( r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_8284])).

cnf(c_8288,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2309,c_8285])).

cnf(c_18854,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5552,c_34,c_654,c_2474,c_3516,c_3521,c_3554,c_3644,c_4125,c_4440,c_4448,c_5538,c_5547,c_5840,c_6555,c_6635,c_8288])).

cnf(c_3480,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),X1) = iProver_top
    | r1_tarski(sK7,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_2315])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2310,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4643,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_2310])).

cnf(c_4945,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4643,c_34,c_2474])).

cnf(c_4946,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4945])).

cnf(c_4953,plain,
    ( k1_funct_1(sK7,sK1(k1_funct_1(sK7,X0),X1,sK7)) = k1_funct_1(sK7,X0)
    | r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4946,c_4015])).

cnf(c_6469,plain,
    ( k1_funct_1(sK7,sK1(k1_funct_1(sK7,k4_tarski(X0,k1_funct_1(sK7,X0))),X1,sK7)) = k1_funct_1(sK7,k4_tarski(X0,k1_funct_1(sK7,X0)))
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),X1) != iProver_top
    | r1_tarski(sK7,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3480,c_4953])).

cnf(c_12686,plain,
    ( k1_funct_1(sK7,sK1(k1_funct_1(sK7,k4_tarski(X0,k1_funct_1(sK7,X0))),sK7,sK7)) = k1_funct_1(sK7,k4_tarski(X0,k1_funct_1(sK7,X0)))
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r1_tarski(sK7,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2735,c_6469])).

cnf(c_18899,plain,
    ( k1_funct_1(k1_xboole_0,sK1(k1_funct_1(k1_xboole_0,k4_tarski(X0,k1_funct_1(k1_xboole_0,X0))),k1_xboole_0,k1_xboole_0)) = k1_funct_1(k1_xboole_0,k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)))
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18854,c_12686])).

cnf(c_1724,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_3193,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3194,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3193])).

cnf(c_1708,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_3552,plain,
    ( k1_relat_1(sK7) = k1_relat_1(X0)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_3553,plain,
    ( k1_relat_1(sK7) = k1_relat_1(k1_xboole_0)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3552])).

cnf(c_3735,plain,
    ( X0 != sK5
    | k1_relat_1(sK7) = X0
    | k1_relat_1(sK7) != sK5 ),
    inference(instantiation,[status(thm)],[c_2983])).

cnf(c_3742,plain,
    ( k1_relat_1(sK7) != sK5
    | k1_relat_1(sK7) = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3735])).

cnf(c_2470,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3967,plain,
    ( k1_relat_1(X0) != X1
    | sK5 != X1
    | sK5 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2470])).

cnf(c_3972,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK5 = k1_relat_1(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3967])).

cnf(c_2313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3391,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | r2_hidden(sK3(X0,X2),X0) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_2301])).

cnf(c_5757,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = X0
    | r2_hidden(sK3(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2314,c_3391])).

cnf(c_3429,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_2305])).

cnf(c_4792,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2314,c_3429])).

cnf(c_5760,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK3(X0,k1_xboole_0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5757,c_4792])).

cnf(c_5765,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5760])).

cnf(c_3204,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_3734,plain,
    ( k1_relat_1(sK7) != X0
    | k1_relat_1(sK7) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_3204])).

cnf(c_6010,plain,
    ( k1_relat_1(sK7) != k1_relat_1(X0)
    | k1_relat_1(sK7) = sK5
    | sK5 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_3734])).

cnf(c_6011,plain,
    ( k1_relat_1(sK7) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK7) = sK5
    | sK5 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6010])).

cnf(c_2921,plain,
    ( ~ r2_hidden(sK3(X0,X1),X0)
    | r2_hidden(sK3(X0,X1),X2)
    | ~ r1_tarski(X0,X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_10470,plain,
    ( ~ r2_hidden(sK3(X0,X1),X0)
    | r2_hidden(sK3(X0,X1),k1_relat_1(X2))
    | ~ r1_tarski(X0,k1_relat_1(X2)) ),
    inference(instantiation,[status(thm)],[c_2921])).

cnf(c_10475,plain,
    ( r2_hidden(sK3(X0,X1),X0) != iProver_top
    | r2_hidden(sK3(X0,X1),k1_relat_1(X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10470])).

cnf(c_10477,plain,
    ( r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10475])).

cnf(c_4468,plain,
    ( k1_relset_1(X0,X1,sK7) = X0
    | r2_hidden(sK3(X0,sK7),k1_relat_1(sK7)) != iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2313,c_3672])).

cnf(c_18962,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = X0
    | r2_hidden(sK3(X0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18854,c_4468])).

cnf(c_18990,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r2_hidden(sK3(X0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18962,c_4792])).

cnf(c_19279,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18990])).

cnf(c_20488,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_20489,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20488])).

cnf(c_20491,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_20489])).

cnf(c_22368,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18899,c_34,c_654,c_1724,c_2474,c_3194,c_3516,c_3521,c_3553,c_3554,c_3644,c_3742,c_3972,c_4125,c_4440,c_4448,c_5538,c_5547,c_5552,c_5765,c_5840,c_6011,c_6555,c_6635,c_8288,c_10477,c_19279,c_20491])).

cnf(c_22372,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2314,c_22368])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.49/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.49  
% 7.49/1.49  ------  iProver source info
% 7.49/1.49  
% 7.49/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.49  git: non_committed_changes: false
% 7.49/1.49  git: last_make_outside_of_git: false
% 7.49/1.49  
% 7.49/1.49  ------ 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options
% 7.49/1.49  
% 7.49/1.49  --out_options                           all
% 7.49/1.49  --tptp_safe_out                         true
% 7.49/1.49  --problem_path                          ""
% 7.49/1.49  --include_path                          ""
% 7.49/1.49  --clausifier                            res/vclausify_rel
% 7.49/1.49  --clausifier_options                    ""
% 7.49/1.49  --stdin                                 false
% 7.49/1.49  --stats_out                             all
% 7.49/1.49  
% 7.49/1.49  ------ General Options
% 7.49/1.49  
% 7.49/1.49  --fof                                   false
% 7.49/1.49  --time_out_real                         305.
% 7.49/1.49  --time_out_virtual                      -1.
% 7.49/1.49  --symbol_type_check                     false
% 7.49/1.49  --clausify_out                          false
% 7.49/1.49  --sig_cnt_out                           false
% 7.49/1.49  --trig_cnt_out                          false
% 7.49/1.49  --trig_cnt_out_tolerance                1.
% 7.49/1.49  --trig_cnt_out_sk_spl                   false
% 7.49/1.49  --abstr_cl_out                          false
% 7.49/1.49  
% 7.49/1.49  ------ Global Options
% 7.49/1.49  
% 7.49/1.49  --schedule                              default
% 7.49/1.49  --add_important_lit                     false
% 7.49/1.49  --prop_solver_per_cl                    1000
% 7.49/1.49  --min_unsat_core                        false
% 7.49/1.49  --soft_assumptions                      false
% 7.49/1.49  --soft_lemma_size                       3
% 7.49/1.49  --prop_impl_unit_size                   0
% 7.49/1.49  --prop_impl_unit                        []
% 7.49/1.49  --share_sel_clauses                     true
% 7.49/1.49  --reset_solvers                         false
% 7.49/1.49  --bc_imp_inh                            [conj_cone]
% 7.49/1.49  --conj_cone_tolerance                   3.
% 7.49/1.49  --extra_neg_conj                        none
% 7.49/1.49  --large_theory_mode                     true
% 7.49/1.49  --prolific_symb_bound                   200
% 7.49/1.49  --lt_threshold                          2000
% 7.49/1.49  --clause_weak_htbl                      true
% 7.49/1.49  --gc_record_bc_elim                     false
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing Options
% 7.49/1.49  
% 7.49/1.49  --preprocessing_flag                    true
% 7.49/1.49  --time_out_prep_mult                    0.1
% 7.49/1.49  --splitting_mode                        input
% 7.49/1.49  --splitting_grd                         true
% 7.49/1.49  --splitting_cvd                         false
% 7.49/1.49  --splitting_cvd_svl                     false
% 7.49/1.49  --splitting_nvd                         32
% 7.49/1.49  --sub_typing                            true
% 7.49/1.49  --prep_gs_sim                           true
% 7.49/1.49  --prep_unflatten                        true
% 7.49/1.49  --prep_res_sim                          true
% 7.49/1.49  --prep_upred                            true
% 7.49/1.49  --prep_sem_filter                       exhaustive
% 7.49/1.49  --prep_sem_filter_out                   false
% 7.49/1.49  --pred_elim                             true
% 7.49/1.49  --res_sim_input                         true
% 7.49/1.49  --eq_ax_congr_red                       true
% 7.49/1.49  --pure_diseq_elim                       true
% 7.49/1.49  --brand_transform                       false
% 7.49/1.49  --non_eq_to_eq                          false
% 7.49/1.49  --prep_def_merge                        true
% 7.49/1.49  --prep_def_merge_prop_impl              false
% 7.49/1.49  --prep_def_merge_mbd                    true
% 7.49/1.49  --prep_def_merge_tr_red                 false
% 7.49/1.49  --prep_def_merge_tr_cl                  false
% 7.49/1.49  --smt_preprocessing                     true
% 7.49/1.49  --smt_ac_axioms                         fast
% 7.49/1.49  --preprocessed_out                      false
% 7.49/1.49  --preprocessed_stats                    false
% 7.49/1.49  
% 7.49/1.49  ------ Abstraction refinement Options
% 7.49/1.49  
% 7.49/1.49  --abstr_ref                             []
% 7.49/1.49  --abstr_ref_prep                        false
% 7.49/1.49  --abstr_ref_until_sat                   false
% 7.49/1.49  --abstr_ref_sig_restrict                funpre
% 7.49/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.49  --abstr_ref_under                       []
% 7.49/1.49  
% 7.49/1.49  ------ SAT Options
% 7.49/1.49  
% 7.49/1.49  --sat_mode                              false
% 7.49/1.49  --sat_fm_restart_options                ""
% 7.49/1.49  --sat_gr_def                            false
% 7.49/1.49  --sat_epr_types                         true
% 7.49/1.49  --sat_non_cyclic_types                  false
% 7.49/1.49  --sat_finite_models                     false
% 7.49/1.49  --sat_fm_lemmas                         false
% 7.49/1.49  --sat_fm_prep                           false
% 7.49/1.49  --sat_fm_uc_incr                        true
% 7.49/1.49  --sat_out_model                         small
% 7.49/1.49  --sat_out_clauses                       false
% 7.49/1.49  
% 7.49/1.49  ------ QBF Options
% 7.49/1.49  
% 7.49/1.49  --qbf_mode                              false
% 7.49/1.49  --qbf_elim_univ                         false
% 7.49/1.49  --qbf_dom_inst                          none
% 7.49/1.49  --qbf_dom_pre_inst                      false
% 7.49/1.49  --qbf_sk_in                             false
% 7.49/1.49  --qbf_pred_elim                         true
% 7.49/1.49  --qbf_split                             512
% 7.49/1.49  
% 7.49/1.49  ------ BMC1 Options
% 7.49/1.49  
% 7.49/1.49  --bmc1_incremental                      false
% 7.49/1.49  --bmc1_axioms                           reachable_all
% 7.49/1.49  --bmc1_min_bound                        0
% 7.49/1.49  --bmc1_max_bound                        -1
% 7.49/1.49  --bmc1_max_bound_default                -1
% 7.49/1.49  --bmc1_symbol_reachability              true
% 7.49/1.49  --bmc1_property_lemmas                  false
% 7.49/1.49  --bmc1_k_induction                      false
% 7.49/1.49  --bmc1_non_equiv_states                 false
% 7.49/1.49  --bmc1_deadlock                         false
% 7.49/1.49  --bmc1_ucm                              false
% 7.49/1.49  --bmc1_add_unsat_core                   none
% 7.49/1.49  --bmc1_unsat_core_children              false
% 7.49/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.49  --bmc1_out_stat                         full
% 7.49/1.49  --bmc1_ground_init                      false
% 7.49/1.49  --bmc1_pre_inst_next_state              false
% 7.49/1.49  --bmc1_pre_inst_state                   false
% 7.49/1.49  --bmc1_pre_inst_reach_state             false
% 7.49/1.49  --bmc1_out_unsat_core                   false
% 7.49/1.49  --bmc1_aig_witness_out                  false
% 7.49/1.49  --bmc1_verbose                          false
% 7.49/1.49  --bmc1_dump_clauses_tptp                false
% 7.49/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.49  --bmc1_dump_file                        -
% 7.49/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.49  --bmc1_ucm_extend_mode                  1
% 7.49/1.49  --bmc1_ucm_init_mode                    2
% 7.49/1.49  --bmc1_ucm_cone_mode                    none
% 7.49/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.49  --bmc1_ucm_relax_model                  4
% 7.49/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.49  --bmc1_ucm_layered_model                none
% 7.49/1.49  --bmc1_ucm_max_lemma_size               10
% 7.49/1.49  
% 7.49/1.49  ------ AIG Options
% 7.49/1.49  
% 7.49/1.49  --aig_mode                              false
% 7.49/1.49  
% 7.49/1.49  ------ Instantiation Options
% 7.49/1.49  
% 7.49/1.49  --instantiation_flag                    true
% 7.49/1.49  --inst_sos_flag                         true
% 7.49/1.49  --inst_sos_phase                        true
% 7.49/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel_side                     num_symb
% 7.49/1.49  --inst_solver_per_active                1400
% 7.49/1.49  --inst_solver_calls_frac                1.
% 7.49/1.49  --inst_passive_queue_type               priority_queues
% 7.49/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.49  --inst_passive_queues_freq              [25;2]
% 7.49/1.49  --inst_dismatching                      true
% 7.49/1.49  --inst_eager_unprocessed_to_passive     true
% 7.49/1.49  --inst_prop_sim_given                   true
% 7.49/1.49  --inst_prop_sim_new                     false
% 7.49/1.49  --inst_subs_new                         false
% 7.49/1.49  --inst_eq_res_simp                      false
% 7.49/1.49  --inst_subs_given                       false
% 7.49/1.49  --inst_orphan_elimination               true
% 7.49/1.49  --inst_learning_loop_flag               true
% 7.49/1.49  --inst_learning_start                   3000
% 7.49/1.49  --inst_learning_factor                  2
% 7.49/1.49  --inst_start_prop_sim_after_learn       3
% 7.49/1.49  --inst_sel_renew                        solver
% 7.49/1.49  --inst_lit_activity_flag                true
% 7.49/1.49  --inst_restr_to_given                   false
% 7.49/1.49  --inst_activity_threshold               500
% 7.49/1.49  --inst_out_proof                        true
% 7.49/1.49  
% 7.49/1.49  ------ Resolution Options
% 7.49/1.49  
% 7.49/1.49  --resolution_flag                       true
% 7.49/1.49  --res_lit_sel                           adaptive
% 7.49/1.49  --res_lit_sel_side                      none
% 7.49/1.49  --res_ordering                          kbo
% 7.49/1.49  --res_to_prop_solver                    active
% 7.49/1.49  --res_prop_simpl_new                    false
% 7.49/1.49  --res_prop_simpl_given                  true
% 7.49/1.49  --res_passive_queue_type                priority_queues
% 7.49/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.49  --res_passive_queues_freq               [15;5]
% 7.49/1.49  --res_forward_subs                      full
% 7.49/1.49  --res_backward_subs                     full
% 7.49/1.49  --res_forward_subs_resolution           true
% 7.49/1.49  --res_backward_subs_resolution          true
% 7.49/1.49  --res_orphan_elimination                true
% 7.49/1.49  --res_time_limit                        2.
% 7.49/1.49  --res_out_proof                         true
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Options
% 7.49/1.49  
% 7.49/1.49  --superposition_flag                    true
% 7.49/1.49  --sup_passive_queue_type                priority_queues
% 7.49/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.49  --demod_completeness_check              fast
% 7.49/1.49  --demod_use_ground                      true
% 7.49/1.49  --sup_to_prop_solver                    passive
% 7.49/1.49  --sup_prop_simpl_new                    true
% 7.49/1.49  --sup_prop_simpl_given                  true
% 7.49/1.49  --sup_fun_splitting                     true
% 7.49/1.49  --sup_smt_interval                      50000
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Simplification Setup
% 7.49/1.49  
% 7.49/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.49/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.49/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.49/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.49/1.49  --sup_immed_triv                        [TrivRules]
% 7.49/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_bw_main                     []
% 7.49/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.49/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_input_bw                          []
% 7.49/1.49  
% 7.49/1.49  ------ Combination Options
% 7.49/1.49  
% 7.49/1.49  --comb_res_mult                         3
% 7.49/1.49  --comb_sup_mult                         2
% 7.49/1.49  --comb_inst_mult                        10
% 7.49/1.49  
% 7.49/1.49  ------ Debug Options
% 7.49/1.49  
% 7.49/1.49  --dbg_backtrace                         false
% 7.49/1.49  --dbg_dump_prop_clauses                 false
% 7.49/1.49  --dbg_dump_prop_clauses_file            -
% 7.49/1.49  --dbg_out_stat                          false
% 7.49/1.49  ------ Parsing...
% 7.49/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.49  ------ Proving...
% 7.49/1.49  ------ Problem Properties 
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  clauses                                 27
% 7.49/1.49  conjectures                             3
% 7.49/1.49  EPR                                     3
% 7.49/1.49  Horn                                    23
% 7.49/1.49  unary                                   4
% 7.49/1.49  binary                                  8
% 7.49/1.49  lits                                    69
% 7.49/1.49  lits eq                                 14
% 7.49/1.49  fd_pure                                 0
% 7.49/1.49  fd_pseudo                               0
% 7.49/1.49  fd_cond                                 0
% 7.49/1.49  fd_pseudo_cond                          1
% 7.49/1.49  AC symbols                              0
% 7.49/1.49  
% 7.49/1.49  ------ Schedule dynamic 5 is on 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  ------ 
% 7.49/1.49  Current options:
% 7.49/1.49  ------ 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options
% 7.49/1.49  
% 7.49/1.49  --out_options                           all
% 7.49/1.49  --tptp_safe_out                         true
% 7.49/1.49  --problem_path                          ""
% 7.49/1.49  --include_path                          ""
% 7.49/1.49  --clausifier                            res/vclausify_rel
% 7.49/1.49  --clausifier_options                    ""
% 7.49/1.49  --stdin                                 false
% 7.49/1.49  --stats_out                             all
% 7.49/1.49  
% 7.49/1.49  ------ General Options
% 7.49/1.49  
% 7.49/1.49  --fof                                   false
% 7.49/1.49  --time_out_real                         305.
% 7.49/1.49  --time_out_virtual                      -1.
% 7.49/1.49  --symbol_type_check                     false
% 7.49/1.49  --clausify_out                          false
% 7.49/1.49  --sig_cnt_out                           false
% 7.49/1.49  --trig_cnt_out                          false
% 7.49/1.49  --trig_cnt_out_tolerance                1.
% 7.49/1.49  --trig_cnt_out_sk_spl                   false
% 7.49/1.49  --abstr_cl_out                          false
% 7.49/1.49  
% 7.49/1.49  ------ Global Options
% 7.49/1.49  
% 7.49/1.49  --schedule                              default
% 7.49/1.49  --add_important_lit                     false
% 7.49/1.49  --prop_solver_per_cl                    1000
% 7.49/1.49  --min_unsat_core                        false
% 7.49/1.49  --soft_assumptions                      false
% 7.49/1.49  --soft_lemma_size                       3
% 7.49/1.49  --prop_impl_unit_size                   0
% 7.49/1.49  --prop_impl_unit                        []
% 7.49/1.49  --share_sel_clauses                     true
% 7.49/1.49  --reset_solvers                         false
% 7.49/1.49  --bc_imp_inh                            [conj_cone]
% 7.49/1.49  --conj_cone_tolerance                   3.
% 7.49/1.49  --extra_neg_conj                        none
% 7.49/1.49  --large_theory_mode                     true
% 7.49/1.49  --prolific_symb_bound                   200
% 7.49/1.49  --lt_threshold                          2000
% 7.49/1.49  --clause_weak_htbl                      true
% 7.49/1.49  --gc_record_bc_elim                     false
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing Options
% 7.49/1.49  
% 7.49/1.49  --preprocessing_flag                    true
% 7.49/1.49  --time_out_prep_mult                    0.1
% 7.49/1.49  --splitting_mode                        input
% 7.49/1.49  --splitting_grd                         true
% 7.49/1.49  --splitting_cvd                         false
% 7.49/1.49  --splitting_cvd_svl                     false
% 7.49/1.49  --splitting_nvd                         32
% 7.49/1.49  --sub_typing                            true
% 7.49/1.49  --prep_gs_sim                           true
% 7.49/1.49  --prep_unflatten                        true
% 7.49/1.49  --prep_res_sim                          true
% 7.49/1.49  --prep_upred                            true
% 7.49/1.49  --prep_sem_filter                       exhaustive
% 7.49/1.49  --prep_sem_filter_out                   false
% 7.49/1.49  --pred_elim                             true
% 7.49/1.49  --res_sim_input                         true
% 7.49/1.49  --eq_ax_congr_red                       true
% 7.49/1.49  --pure_diseq_elim                       true
% 7.49/1.49  --brand_transform                       false
% 7.49/1.49  --non_eq_to_eq                          false
% 7.49/1.49  --prep_def_merge                        true
% 7.49/1.49  --prep_def_merge_prop_impl              false
% 7.49/1.49  --prep_def_merge_mbd                    true
% 7.49/1.49  --prep_def_merge_tr_red                 false
% 7.49/1.49  --prep_def_merge_tr_cl                  false
% 7.49/1.49  --smt_preprocessing                     true
% 7.49/1.49  --smt_ac_axioms                         fast
% 7.49/1.49  --preprocessed_out                      false
% 7.49/1.49  --preprocessed_stats                    false
% 7.49/1.49  
% 7.49/1.49  ------ Abstraction refinement Options
% 7.49/1.49  
% 7.49/1.49  --abstr_ref                             []
% 7.49/1.49  --abstr_ref_prep                        false
% 7.49/1.49  --abstr_ref_until_sat                   false
% 7.49/1.49  --abstr_ref_sig_restrict                funpre
% 7.49/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.49  --abstr_ref_under                       []
% 7.49/1.49  
% 7.49/1.49  ------ SAT Options
% 7.49/1.49  
% 7.49/1.49  --sat_mode                              false
% 7.49/1.49  --sat_fm_restart_options                ""
% 7.49/1.49  --sat_gr_def                            false
% 7.49/1.49  --sat_epr_types                         true
% 7.49/1.49  --sat_non_cyclic_types                  false
% 7.49/1.49  --sat_finite_models                     false
% 7.49/1.49  --sat_fm_lemmas                         false
% 7.49/1.49  --sat_fm_prep                           false
% 7.49/1.49  --sat_fm_uc_incr                        true
% 7.49/1.49  --sat_out_model                         small
% 7.49/1.49  --sat_out_clauses                       false
% 7.49/1.49  
% 7.49/1.49  ------ QBF Options
% 7.49/1.49  
% 7.49/1.49  --qbf_mode                              false
% 7.49/1.49  --qbf_elim_univ                         false
% 7.49/1.49  --qbf_dom_inst                          none
% 7.49/1.49  --qbf_dom_pre_inst                      false
% 7.49/1.49  --qbf_sk_in                             false
% 7.49/1.49  --qbf_pred_elim                         true
% 7.49/1.49  --qbf_split                             512
% 7.49/1.49  
% 7.49/1.49  ------ BMC1 Options
% 7.49/1.49  
% 7.49/1.49  --bmc1_incremental                      false
% 7.49/1.49  --bmc1_axioms                           reachable_all
% 7.49/1.49  --bmc1_min_bound                        0
% 7.49/1.49  --bmc1_max_bound                        -1
% 7.49/1.49  --bmc1_max_bound_default                -1
% 7.49/1.49  --bmc1_symbol_reachability              true
% 7.49/1.49  --bmc1_property_lemmas                  false
% 7.49/1.49  --bmc1_k_induction                      false
% 7.49/1.49  --bmc1_non_equiv_states                 false
% 7.49/1.49  --bmc1_deadlock                         false
% 7.49/1.49  --bmc1_ucm                              false
% 7.49/1.49  --bmc1_add_unsat_core                   none
% 7.49/1.49  --bmc1_unsat_core_children              false
% 7.49/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.49  --bmc1_out_stat                         full
% 7.49/1.49  --bmc1_ground_init                      false
% 7.49/1.49  --bmc1_pre_inst_next_state              false
% 7.49/1.49  --bmc1_pre_inst_state                   false
% 7.49/1.49  --bmc1_pre_inst_reach_state             false
% 7.49/1.49  --bmc1_out_unsat_core                   false
% 7.49/1.49  --bmc1_aig_witness_out                  false
% 7.49/1.49  --bmc1_verbose                          false
% 7.49/1.49  --bmc1_dump_clauses_tptp                false
% 7.49/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.49  --bmc1_dump_file                        -
% 7.49/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.49  --bmc1_ucm_extend_mode                  1
% 7.49/1.49  --bmc1_ucm_init_mode                    2
% 7.49/1.49  --bmc1_ucm_cone_mode                    none
% 7.49/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.49  --bmc1_ucm_relax_model                  4
% 7.49/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.49  --bmc1_ucm_layered_model                none
% 7.49/1.49  --bmc1_ucm_max_lemma_size               10
% 7.49/1.49  
% 7.49/1.49  ------ AIG Options
% 7.49/1.49  
% 7.49/1.49  --aig_mode                              false
% 7.49/1.49  
% 7.49/1.49  ------ Instantiation Options
% 7.49/1.49  
% 7.49/1.49  --instantiation_flag                    true
% 7.49/1.49  --inst_sos_flag                         true
% 7.49/1.49  --inst_sos_phase                        true
% 7.49/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel_side                     none
% 7.49/1.49  --inst_solver_per_active                1400
% 7.49/1.49  --inst_solver_calls_frac                1.
% 7.49/1.49  --inst_passive_queue_type               priority_queues
% 7.49/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.49  --inst_passive_queues_freq              [25;2]
% 7.49/1.49  --inst_dismatching                      true
% 7.49/1.49  --inst_eager_unprocessed_to_passive     true
% 7.49/1.49  --inst_prop_sim_given                   true
% 7.49/1.49  --inst_prop_sim_new                     false
% 7.49/1.49  --inst_subs_new                         false
% 7.49/1.49  --inst_eq_res_simp                      false
% 7.49/1.49  --inst_subs_given                       false
% 7.49/1.49  --inst_orphan_elimination               true
% 7.49/1.49  --inst_learning_loop_flag               true
% 7.49/1.49  --inst_learning_start                   3000
% 7.49/1.49  --inst_learning_factor                  2
% 7.49/1.49  --inst_start_prop_sim_after_learn       3
% 7.49/1.49  --inst_sel_renew                        solver
% 7.49/1.49  --inst_lit_activity_flag                true
% 7.49/1.49  --inst_restr_to_given                   false
% 7.49/1.49  --inst_activity_threshold               500
% 7.49/1.49  --inst_out_proof                        true
% 7.49/1.49  
% 7.49/1.49  ------ Resolution Options
% 7.49/1.49  
% 7.49/1.49  --resolution_flag                       false
% 7.49/1.49  --res_lit_sel                           adaptive
% 7.49/1.49  --res_lit_sel_side                      none
% 7.49/1.49  --res_ordering                          kbo
% 7.49/1.49  --res_to_prop_solver                    active
% 7.49/1.49  --res_prop_simpl_new                    false
% 7.49/1.49  --res_prop_simpl_given                  true
% 7.49/1.49  --res_passive_queue_type                priority_queues
% 7.49/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.49  --res_passive_queues_freq               [15;5]
% 7.49/1.49  --res_forward_subs                      full
% 7.49/1.49  --res_backward_subs                     full
% 7.49/1.49  --res_forward_subs_resolution           true
% 7.49/1.49  --res_backward_subs_resolution          true
% 7.49/1.49  --res_orphan_elimination                true
% 7.49/1.49  --res_time_limit                        2.
% 7.49/1.49  --res_out_proof                         true
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Options
% 7.49/1.49  
% 7.49/1.49  --superposition_flag                    true
% 7.49/1.49  --sup_passive_queue_type                priority_queues
% 7.49/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.49  --demod_completeness_check              fast
% 7.49/1.49  --demod_use_ground                      true
% 7.49/1.49  --sup_to_prop_solver                    passive
% 7.49/1.49  --sup_prop_simpl_new                    true
% 7.49/1.49  --sup_prop_simpl_given                  true
% 7.49/1.49  --sup_fun_splitting                     true
% 7.49/1.49  --sup_smt_interval                      50000
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Simplification Setup
% 7.49/1.49  
% 7.49/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.49/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.49/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.49/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.49/1.49  --sup_immed_triv                        [TrivRules]
% 7.49/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_bw_main                     []
% 7.49/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.49/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_input_bw                          []
% 7.49/1.49  
% 7.49/1.49  ------ Combination Options
% 7.49/1.49  
% 7.49/1.49  --comb_res_mult                         3
% 7.49/1.49  --comb_sup_mult                         2
% 7.49/1.49  --comb_inst_mult                        10
% 7.49/1.49  
% 7.49/1.49  ------ Debug Options
% 7.49/1.49  
% 7.49/1.49  --dbg_backtrace                         false
% 7.49/1.49  --dbg_dump_prop_clauses                 false
% 7.49/1.49  --dbg_dump_prop_clauses_file            -
% 7.49/1.49  --dbg_out_stat                          false
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  ------ Proving...
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  % SZS status Theorem for theBenchmark.p
% 7.49/1.49  
% 7.49/1.49   Resolution empty clause
% 7.49/1.49  
% 7.49/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  fof(f2,axiom,(
% 7.49/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f51,plain,(
% 7.49/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f2])).
% 7.49/1.49  
% 7.49/1.49  fof(f12,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f24,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(ennf_transformation,[],[f12])).
% 7.49/1.49  
% 7.49/1.49  fof(f25,plain,(
% 7.49/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(flattening,[],[f24])).
% 7.49/1.49  
% 7.49/1.49  fof(f44,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(nnf_transformation,[],[f25])).
% 7.49/1.49  
% 7.49/1.49  fof(f69,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f44])).
% 7.49/1.49  
% 7.49/1.49  fof(f13,conjecture,(
% 7.49/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f14,negated_conjecture,(
% 7.49/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.49/1.49    inference(negated_conjecture,[],[f13])).
% 7.49/1.49  
% 7.49/1.49  fof(f26,plain,(
% 7.49/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.49/1.49    inference(ennf_transformation,[],[f14])).
% 7.49/1.49  
% 7.49/1.49  fof(f27,plain,(
% 7.49/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.49/1.49    inference(flattening,[],[f26])).
% 7.49/1.49  
% 7.49/1.49  fof(f46,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f45,plain,(
% 7.49/1.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f47,plain,(
% 7.49/1.49    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 7.49/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f27,f46,f45])).
% 7.49/1.49  
% 7.49/1.49  fof(f76,plain,(
% 7.49/1.49    v1_funct_2(sK7,sK4,sK5)),
% 7.49/1.49    inference(cnf_transformation,[],[f47])).
% 7.49/1.49  
% 7.49/1.49  fof(f77,plain,(
% 7.49/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 7.49/1.49    inference(cnf_transformation,[],[f47])).
% 7.49/1.49  
% 7.49/1.49  fof(f11,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f23,plain,(
% 7.49/1.49    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.49/1.49    inference(ennf_transformation,[],[f11])).
% 7.49/1.49  
% 7.49/1.49  fof(f39,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.49/1.49    inference(nnf_transformation,[],[f23])).
% 7.49/1.49  
% 7.49/1.49  fof(f40,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.49/1.49    inference(rectify,[],[f39])).
% 7.49/1.49  
% 7.49/1.49  fof(f42,plain,(
% 7.49/1.49    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f41,plain,(
% 7.49/1.49    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f43,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 7.49/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 7.49/1.49  
% 7.49/1.49  fof(f68,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1) | k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f43])).
% 7.49/1.49  
% 7.49/1.49  fof(f9,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f21,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(ennf_transformation,[],[f9])).
% 7.49/1.49  
% 7.49/1.49  fof(f64,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f21])).
% 7.49/1.49  
% 7.49/1.49  fof(f1,axiom,(
% 7.49/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f15,plain,(
% 7.49/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f1])).
% 7.49/1.49  
% 7.49/1.49  fof(f28,plain,(
% 7.49/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.49/1.49    inference(nnf_transformation,[],[f15])).
% 7.49/1.49  
% 7.49/1.49  fof(f29,plain,(
% 7.49/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.49/1.49    inference(rectify,[],[f28])).
% 7.49/1.49  
% 7.49/1.49  fof(f30,plain,(
% 7.49/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f31,plain,(
% 7.49/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.49/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 7.49/1.49  
% 7.49/1.49  fof(f48,plain,(
% 7.49/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f31])).
% 7.49/1.49  
% 7.49/1.49  fof(f8,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f20,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(ennf_transformation,[],[f8])).
% 7.49/1.49  
% 7.49/1.49  fof(f63,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f20])).
% 7.49/1.49  
% 7.49/1.49  fof(f10,axiom,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f22,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.49/1.49    inference(ennf_transformation,[],[f10])).
% 7.49/1.49  
% 7.49/1.49  fof(f65,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f22])).
% 7.49/1.49  
% 7.49/1.49  fof(f78,plain,(
% 7.49/1.49    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 7.49/1.49    inference(cnf_transformation,[],[f47])).
% 7.49/1.49  
% 7.49/1.49  fof(f6,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f17,plain,(
% 7.49/1.49    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.49/1.49    inference(ennf_transformation,[],[f6])).
% 7.49/1.49  
% 7.49/1.49  fof(f33,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.49/1.49    inference(nnf_transformation,[],[f17])).
% 7.49/1.49  
% 7.49/1.49  fof(f34,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.49/1.49    inference(rectify,[],[f33])).
% 7.49/1.49  
% 7.49/1.49  fof(f35,plain,(
% 7.49/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f36,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.49/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 7.49/1.49  
% 7.49/1.49  fof(f58,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f36])).
% 7.49/1.49  
% 7.49/1.49  fof(f56,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f36])).
% 7.49/1.49  
% 7.49/1.49  fof(f57,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f36])).
% 7.49/1.49  
% 7.49/1.49  fof(f7,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f18,plain,(
% 7.49/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.49/1.49    inference(ennf_transformation,[],[f7])).
% 7.49/1.49  
% 7.49/1.49  fof(f19,plain,(
% 7.49/1.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.49/1.49    inference(flattening,[],[f18])).
% 7.49/1.49  
% 7.49/1.49  fof(f37,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.49/1.49    inference(nnf_transformation,[],[f19])).
% 7.49/1.49  
% 7.49/1.49  fof(f38,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.49/1.49    inference(flattening,[],[f37])).
% 7.49/1.49  
% 7.49/1.49  fof(f61,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f38])).
% 7.49/1.49  
% 7.49/1.49  fof(f75,plain,(
% 7.49/1.49    v1_funct_1(sK7)),
% 7.49/1.49    inference(cnf_transformation,[],[f47])).
% 7.49/1.49  
% 7.49/1.49  fof(f79,plain,(
% 7.49/1.49    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~r2_hidden(X5,sK4)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f47])).
% 7.49/1.49  
% 7.49/1.49  fof(f73,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f44])).
% 7.49/1.49  
% 7.49/1.49  fof(f83,plain,(
% 7.49/1.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.49/1.49    inference(equality_resolution,[],[f73])).
% 7.49/1.49  
% 7.49/1.49  fof(f3,axiom,(
% 7.49/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f32,plain,(
% 7.49/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.49/1.49    inference(nnf_transformation,[],[f3])).
% 7.49/1.49  
% 7.49/1.49  fof(f53,plain,(
% 7.49/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f32])).
% 7.49/1.49  
% 7.49/1.49  fof(f52,plain,(
% 7.49/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f32])).
% 7.49/1.49  
% 7.49/1.49  fof(f66,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK3(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f43])).
% 7.49/1.49  
% 7.49/1.49  fof(f62,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f38])).
% 7.49/1.49  
% 7.49/1.49  fof(f80,plain,(
% 7.49/1.49    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.49/1.49    inference(equality_resolution,[],[f62])).
% 7.49/1.49  
% 7.49/1.49  fof(f67,plain,(
% 7.49/1.49    ( ! [X6,X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f43])).
% 7.49/1.49  
% 7.49/1.49  fof(f59,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f36])).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3,plain,
% 7.49/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2314,plain,
% 7.49/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_26,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.49/1.49      | k1_xboole_0 = X2 ),
% 7.49/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_30,negated_conjecture,
% 7.49/1.49      ( v1_funct_2(sK7,sK4,sK5) ),
% 7.49/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_685,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.49/1.49      | sK5 != X2
% 7.49/1.49      | sK4 != X1
% 7.49/1.49      | sK7 != X0
% 7.49/1.49      | k1_xboole_0 = X2 ),
% 7.49/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_686,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 7.49/1.49      | k1_relset_1(sK4,sK5,sK7) = sK4
% 7.49/1.49      | k1_xboole_0 = sK5 ),
% 7.49/1.49      inference(unflattening,[status(thm)],[c_685]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_29,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 7.49/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_688,plain,
% 7.49/1.49      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 7.49/1.49      inference(global_propositional_subsumption,[status(thm)],[c_686,c_29]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_18,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ r2_hidden(X3,X1)
% 7.49/1.49      | r2_hidden(k4_tarski(X3,sK2(X0,X3)),X0)
% 7.49/1.49      | k1_relset_1(X1,X2,X0) != X1 ),
% 7.49/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2303,plain,
% 7.49/1.49      ( k1_relset_1(X0,X1,X2) != X0
% 7.49/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.49      | r2_hidden(X3,X0) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3846,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 7.49/1.49      | r2_hidden(X0,sK4) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_688,c_2303]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_34,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2298,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2305,plain,
% 7.49/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.49/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3430,plain,
% 7.49/1.49      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2298,c_2305]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3489,plain,
% 7.49/1.49      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_688,c_3430]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3845,plain,
% 7.49/1.49      ( k1_relat_1(sK7) != sK4
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 7.49/1.49      | r2_hidden(X0,sK4) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3430,c_2303]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3991,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0
% 7.49/1.49      | r2_hidden(X0,sK4) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),sK7) = iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3846,c_34,c_3489,c_3845]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.49/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2315,plain,
% 7.49/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.49/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.49/1.49      | r1_tarski(X1,X2) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3997,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0
% 7.49/1.49      | r2_hidden(X0,sK4) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(X0,sK2(sK7,X0)),X1) = iProver_top
% 7.49/1.49      | r1_tarski(sK7,X1) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3991,c_2315]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_15,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2384,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK7) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2473,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 7.49/1.49      | v1_relat_1(sK7) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2384]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2474,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 7.49/1.49      | v1_relat_1(sK7) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_2473]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2304,plain,
% 7.49/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.49/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3436,plain,
% 7.49/1.49      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2298,c_2304]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_28,negated_conjecture,
% 7.49/1.49      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2299,plain,
% 7.49/1.49      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3516,plain,
% 7.49/1.49      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_3436,c_2299]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_9,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.49/1.49      | r2_hidden(sK1(X0,X2,X1),X2)
% 7.49/1.49      | ~ v1_relat_1(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2309,plain,
% 7.49/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.49/1.49      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 7.49/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_11,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.49/1.49      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 7.49/1.49      | ~ v1_relat_1(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2307,plain,
% 7.49/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.49/1.49      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 7.49/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3775,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0
% 7.49/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.49/1.49      | r2_hidden(sK1(X0,X1,sK7),sK4) = iProver_top
% 7.49/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3489,c_2307]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5311,plain,
% 7.49/1.49      ( r2_hidden(sK1(X0,X1,sK7),sK4) = iProver_top
% 7.49/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.49/1.49      | sK5 = k1_xboole_0 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3775,c_34,c_2474]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5312,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0
% 7.49/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.49/1.49      | r2_hidden(sK1(X0,X1,sK7),sK4) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_5311]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_10,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.49/1.49      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 7.49/1.49      | ~ v1_relat_1(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2308,plain,
% 7.49/1.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 7.49/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13,plain,
% 7.49/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.49/1.49      | ~ v1_funct_1(X2)
% 7.49/1.49      | ~ v1_relat_1(X2)
% 7.49/1.49      | k1_funct_1(X2,X0) = X1 ),
% 7.49/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_31,negated_conjecture,
% 7.49/1.49      ( v1_funct_1(sK7) ),
% 7.49/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_455,plain,
% 7.49/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.49/1.49      | ~ v1_relat_1(X2)
% 7.49/1.49      | k1_funct_1(X2,X0) = X1
% 7.49/1.49      | sK7 != X2 ),
% 7.49/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_31]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_456,plain,
% 7.49/1.49      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 7.49/1.49      | ~ v1_relat_1(sK7)
% 7.49/1.49      | k1_funct_1(sK7,X0) = X1 ),
% 7.49/1.49      inference(unflattening,[status(thm)],[c_455]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2294,plain,
% 7.49/1.49      ( k1_funct_1(sK7,X0) = X1
% 7.49/1.49      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 7.49/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_457,plain,
% 7.49/1.49      ( k1_funct_1(sK7,X0) = X1
% 7.49/1.49      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 7.49/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2661,plain,
% 7.49/1.49      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 7.49/1.49      | k1_funct_1(sK7,X0) = X1 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_2294,c_34,c_457,c_2474]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2662,plain,
% 7.49/1.49      ( k1_funct_1(sK7,X0) = X1
% 7.49/1.49      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_2661]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3839,plain,
% 7.49/1.49      ( k1_funct_1(sK7,sK1(X0,X1,sK7)) = X0
% 7.49/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.49/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2308,c_2662]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4014,plain,
% 7.49/1.49      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.49/1.49      | k1_funct_1(sK7,sK1(X0,X1,sK7)) = X0 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3839,c_34,c_2474]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4015,plain,
% 7.49/1.49      ( k1_funct_1(sK7,sK1(X0,X1,sK7)) = X0
% 7.49/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_4014]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4024,plain,
% 7.49/1.49      ( k1_funct_1(sK7,sK1(sK8,sK6,sK7)) = sK8 ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3516,c_4015]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_27,negated_conjecture,
% 7.49/1.49      ( ~ r2_hidden(X0,sK4) | ~ r2_hidden(X0,sK6) | k1_funct_1(sK7,X0) != sK8 ),
% 7.49/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2300,plain,
% 7.49/1.49      ( k1_funct_1(sK7,X0) != sK8
% 7.49/1.49      | r2_hidden(X0,sK4) != iProver_top
% 7.49/1.49      | r2_hidden(X0,sK6) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4100,plain,
% 7.49/1.49      ( r2_hidden(sK1(sK8,sK6,sK7),sK4) != iProver_top
% 7.49/1.49      | r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_4024,c_2300]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5319,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0
% 7.49/1.49      | r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top
% 7.49/1.49      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_5312,c_4100]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5534,plain,
% 7.49/1.49      ( r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top | sK5 = k1_xboole_0 ),
% 7.49/1.49      inference(global_propositional_subsumption,[status(thm)],[c_5319,c_3516]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5535,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0 | r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_5534]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5538,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0
% 7.49/1.49      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 7.49/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2309,c_5535]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5541,plain,
% 7.49/1.49      ( sK5 = k1_xboole_0 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3997,c_34,c_2474,c_3516,c_5538]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_22,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.49/1.49      | k1_xboole_0 = X1
% 7.49/1.49      | k1_xboole_0 = X0 ),
% 7.49/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_652,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.49/1.49      | sK5 != k1_xboole_0
% 7.49/1.49      | sK4 != X1
% 7.49/1.49      | sK7 != X0
% 7.49/1.49      | k1_xboole_0 = X0
% 7.49/1.49      | k1_xboole_0 = X1 ),
% 7.49/1.49      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_653,plain,
% 7.49/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
% 7.49/1.49      | sK5 != k1_xboole_0
% 7.49/1.49      | k1_xboole_0 = sK4
% 7.49/1.49      | k1_xboole_0 = sK7 ),
% 7.49/1.49      inference(unflattening,[status(thm)],[c_652]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2293,plain,
% 7.49/1.49      ( sK5 != k1_xboole_0
% 7.49/1.49      | k1_xboole_0 = sK4
% 7.49/1.49      | k1_xboole_0 = sK7
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5548,plain,
% 7.49/1.49      ( sK4 = k1_xboole_0
% 7.49/1.49      | sK7 = k1_xboole_0
% 7.49/1.49      | k1_xboole_0 != k1_xboole_0
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_5541,c_2293]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5552,plain,
% 7.49/1.49      ( sK4 = k1_xboole_0
% 7.49/1.49      | sK7 = k1_xboole_0
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 7.49/1.49      inference(equality_resolution_simp,[status(thm)],[c_5548]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_654,plain,
% 7.49/1.49      ( sK5 != k1_xboole_0
% 7.49/1.49      | k1_xboole_0 = sK4
% 7.49/1.49      | k1_xboole_0 = sK7
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1700,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3030,plain,
% 7.49/1.49      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1700]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3520,plain,
% 7.49/1.49      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_3030]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3521,plain,
% 7.49/1.49      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_3520]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1699,plain,( X0 = X0 ),theory(equality) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3554,plain,
% 7.49/1.49      ( sK7 = sK7 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1699]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4,plain,
% 7.49/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2476,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.49      | ~ r1_tarski(sK7,k2_zfmisc_1(X0,X1)) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3643,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)))
% 7.49/1.49      | ~ r1_tarski(sK7,k2_zfmisc_1(sK4,k1_xboole_0)) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2476]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3644,plain,
% 7.49/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top
% 7.49/1.49      | r1_tarski(sK7,k2_zfmisc_1(sK4,k1_xboole_0)) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_3643]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1701,plain,
% 7.49/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.49/1.49      theory(equality) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2865,plain,
% 7.49/1.49      ( ~ r1_tarski(X0,k1_relat_1(sK7))
% 7.49/1.49      | r1_tarski(X1,k1_relat_1(sK7))
% 7.49/1.49      | X1 != X0 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1701]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4123,plain,
% 7.49/1.49      ( ~ r1_tarski(X0,k1_relat_1(sK7))
% 7.49/1.49      | r1_tarski(sK4,k1_relat_1(sK7))
% 7.49/1.49      | sK4 != X0 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2865]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4125,plain,
% 7.49/1.49      ( r1_tarski(sK4,k1_relat_1(sK7))
% 7.49/1.49      | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK7))
% 7.49/1.49      | sK4 != k1_xboole_0 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_4123]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4440,plain,
% 7.49/1.49      ( r1_tarski(k1_xboole_0,k1_relat_1(sK7)) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4447,plain,
% 7.49/1.49      ( r1_tarski(k1_xboole_0,sK4) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4448,plain,
% 7.49/1.49      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_4447]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2312,plain,
% 7.49/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.49/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3016,plain,
% 7.49/1.49      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2298,c_2312]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5547,plain,
% 7.49/1.49      ( r1_tarski(sK7,k2_zfmisc_1(sK4,k1_xboole_0)) = iProver_top ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_5541,c_3016]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_20,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | r2_hidden(sK3(X1,X0),X1)
% 7.49/1.49      | k1_relset_1(X1,X2,X0) = X1 ),
% 7.49/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2301,plain,
% 7.49/1.49      ( k1_relset_1(X0,X1,X2) = X0
% 7.49/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.49      | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3392,plain,
% 7.49/1.49      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 7.49/1.49      | r2_hidden(sK3(sK4,sK7),sK4) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2298,c_2301]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3544,plain,
% 7.49/1.49      ( k1_relat_1(sK7) = sK4 | r2_hidden(sK3(sK4,sK7),sK4) = iProver_top ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_3392,c_3430]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3546,plain,
% 7.49/1.49      ( k1_relat_1(sK7) = sK4
% 7.49/1.49      | r2_hidden(sK3(sK4,sK7),X0) = iProver_top
% 7.49/1.49      | r1_tarski(sK4,X0) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_3544,c_2315]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.49/1.49      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.49/1.49      | ~ v1_funct_1(X1)
% 7.49/1.49      | ~ v1_relat_1(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_440,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.49/1.49      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.49/1.49      | ~ v1_relat_1(X1)
% 7.49/1.49      | sK7 != X1 ),
% 7.49/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_441,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 7.49/1.49      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
% 7.49/1.49      | ~ v1_relat_1(sK7) ),
% 7.49/1.49      inference(unflattening,[status(thm)],[c_440]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2295,plain,
% 7.49/1.49      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 7.49/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_442,plain,
% 7.49/1.49      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 7.49/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2734,plain,
% 7.49/1.49      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 7.49/1.49      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_2295,c_34,c_442,c_2474]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2735,plain,
% 7.49/1.49      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_2734]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_19,plain,
% 7.49/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ r2_hidden(k4_tarski(sK3(X1,X0),X3),X0)
% 7.49/1.49      | k1_relset_1(X1,X2,X0) = X1 ),
% 7.49/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2302,plain,
% 7.49/1.49      ( k1_relset_1(X0,X1,X2) = X0
% 7.49/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.49      | r2_hidden(k4_tarski(sK3(X0,X2),X3),X2) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3672,plain,
% 7.49/1.49      ( k1_relset_1(X0,X1,sK7) = X0
% 7.49/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.49/1.49      | r2_hidden(sK3(X0,sK7),k1_relat_1(sK7)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2735,c_2302]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4469,plain,
% 7.49/1.49      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 7.49/1.49      | r2_hidden(sK3(sK4,sK7),k1_relat_1(sK7)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_2298,c_3672]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4470,plain,
% 7.49/1.49      ( k1_relat_1(sK7) = sK4
% 7.49/1.49      | r2_hidden(sK3(sK4,sK7),k1_relat_1(sK7)) != iProver_top ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_4469,c_3430]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5835,plain,
% 7.49/1.49      ( k1_relat_1(sK7) = sK4 | r1_tarski(sK4,k1_relat_1(sK7)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3546,c_4470]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5840,plain,
% 7.49/1.50      ( ~ r1_tarski(sK4,k1_relat_1(sK7)) | k1_relat_1(sK7) = sK4 ),
% 7.49/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5835]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2441,plain,
% 7.49/1.50      ( ~ r1_tarski(X0,sK4) | r1_tarski(X1,sK4) | X1 != X0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1701]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3043,plain,
% 7.49/1.50      ( ~ r1_tarski(X0,sK4)
% 7.49/1.50      | r1_tarski(k1_relat_1(X1),sK4)
% 7.49/1.50      | k1_relat_1(X1) != X0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_2441]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6550,plain,
% 7.49/1.50      ( ~ r1_tarski(X0,sK4)
% 7.49/1.50      | r1_tarski(k1_relat_1(sK7),sK4)
% 7.49/1.50      | k1_relat_1(sK7) != X0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_3043]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6553,plain,
% 7.49/1.50      ( k1_relat_1(sK7) != X0
% 7.49/1.50      | r1_tarski(X0,sK4) != iProver_top
% 7.49/1.50      | r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_6550]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6555,plain,
% 7.49/1.50      ( k1_relat_1(sK7) != k1_xboole_0
% 7.49/1.50      | r1_tarski(k1_relat_1(sK7),sK4) = iProver_top
% 7.49/1.50      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_6553]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2983,plain,
% 7.49/1.50      ( X0 != X1 | k1_relat_1(sK7) != X1 | k1_relat_1(sK7) = X0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1700]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6628,plain,
% 7.49/1.50      ( X0 != sK4 | k1_relat_1(sK7) = X0 | k1_relat_1(sK7) != sK4 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_2983]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6635,plain,
% 7.49/1.50      ( k1_relat_1(sK7) != sK4
% 7.49/1.50      | k1_relat_1(sK7) = k1_xboole_0
% 7.49/1.50      | k1_xboole_0 != sK4 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_6628]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3776,plain,
% 7.49/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.49/1.50      | r2_hidden(sK1(X0,X2,X1),X3) = iProver_top
% 7.49/1.50      | r1_tarski(k1_relat_1(X1),X3) != iProver_top
% 7.49/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2307,c_2315]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_7823,plain,
% 7.49/1.50      ( r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top
% 7.49/1.50      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 7.49/1.50      | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top
% 7.49/1.50      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3776,c_4100]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8284,plain,
% 7.49/1.50      ( r1_tarski(k1_relat_1(sK7),sK4) != iProver_top
% 7.49/1.50      | r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_7823,c_34,c_2474,c_3516]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8285,plain,
% 7.49/1.50      ( r2_hidden(sK1(sK8,sK6,sK7),sK6) != iProver_top
% 7.49/1.50      | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_8284]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8288,plain,
% 7.49/1.50      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 7.49/1.50      | r1_tarski(k1_relat_1(sK7),sK4) != iProver_top
% 7.49/1.50      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2309,c_8285]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18854,plain,
% 7.49/1.50      ( sK7 = k1_xboole_0 ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_5552,c_34,c_654,c_2474,c_3516,c_3521,c_3554,c_3644,c_4125,
% 7.49/1.50                 c_4440,c_4448,c_5538,c_5547,c_5840,c_6555,c_6635,c_8288]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3480,plain,
% 7.49/1.50      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),X1) = iProver_top
% 7.49/1.50      | r1_tarski(sK7,X1) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2735,c_2315]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_8,plain,
% 7.49/1.50      ( ~ r2_hidden(X0,X1)
% 7.49/1.50      | r2_hidden(X2,k9_relat_1(X3,X1))
% 7.49/1.50      | ~ r2_hidden(X0,k1_relat_1(X3))
% 7.49/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 7.49/1.50      | ~ v1_relat_1(X3) ),
% 7.49/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2310,plain,
% 7.49/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.49/1.50      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 7.49/1.50      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 7.49/1.50      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 7.49/1.50      | v1_relat_1(X3) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4643,plain,
% 7.49/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.49/1.50      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.50      | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
% 7.49/1.50      | v1_relat_1(sK7) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2735,c_2310]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4945,plain,
% 7.49/1.50      ( r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
% 7.49/1.50      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.50      | r2_hidden(X0,X1) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_4643,c_34,c_2474]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4946,plain,
% 7.49/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.49/1.50      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.50      | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top ),
% 7.49/1.50      inference(renaming,[status(thm)],[c_4945]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4953,plain,
% 7.49/1.50      ( k1_funct_1(sK7,sK1(k1_funct_1(sK7,X0),X1,sK7)) = k1_funct_1(sK7,X0)
% 7.49/1.50      | r2_hidden(X0,X1) != iProver_top
% 7.49/1.50      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_4946,c_4015]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6469,plain,
% 7.49/1.50      ( k1_funct_1(sK7,sK1(k1_funct_1(sK7,k4_tarski(X0,k1_funct_1(sK7,X0))),X1,sK7)) = k1_funct_1(sK7,k4_tarski(X0,k1_funct_1(sK7,X0)))
% 7.49/1.50      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),X1) != iProver_top
% 7.49/1.50      | r1_tarski(sK7,k1_relat_1(sK7)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_3480,c_4953]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_12686,plain,
% 7.49/1.50      ( k1_funct_1(sK7,sK1(k1_funct_1(sK7,k4_tarski(X0,k1_funct_1(sK7,X0))),sK7,sK7)) = k1_funct_1(sK7,k4_tarski(X0,k1_funct_1(sK7,X0)))
% 7.49/1.50      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.49/1.50      | r1_tarski(sK7,k1_relat_1(sK7)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2735,c_6469]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18899,plain,
% 7.49/1.50      ( k1_funct_1(k1_xboole_0,sK1(k1_funct_1(k1_xboole_0,k4_tarski(X0,k1_funct_1(k1_xboole_0,X0))),k1_xboole_0,k1_xboole_0)) = k1_funct_1(k1_xboole_0,k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)))
% 7.49/1.50      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 7.49/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_18854,c_12686]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1724,plain,
% 7.49/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1699]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3193,plain,
% 7.49/1.50      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1700]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3194,plain,
% 7.49/1.50      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_3193]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_1708,plain,
% 7.49/1.50      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 7.49/1.50      theory(equality) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3552,plain,
% 7.49/1.50      ( k1_relat_1(sK7) = k1_relat_1(X0) | sK7 != X0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1708]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3553,plain,
% 7.49/1.50      ( k1_relat_1(sK7) = k1_relat_1(k1_xboole_0) | sK7 != k1_xboole_0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_3552]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3735,plain,
% 7.49/1.50      ( X0 != sK5 | k1_relat_1(sK7) = X0 | k1_relat_1(sK7) != sK5 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_2983]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3742,plain,
% 7.49/1.50      ( k1_relat_1(sK7) != sK5
% 7.49/1.50      | k1_relat_1(sK7) = k1_xboole_0
% 7.49/1.50      | k1_xboole_0 != sK5 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_3735]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2470,plain,
% 7.49/1.50      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1700]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3967,plain,
% 7.49/1.50      ( k1_relat_1(X0) != X1 | sK5 != X1 | sK5 = k1_relat_1(X0) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_2470]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3972,plain,
% 7.49/1.50      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 7.49/1.50      | sK5 = k1_relat_1(k1_xboole_0)
% 7.49/1.50      | sK5 != k1_xboole_0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_3967]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2313,plain,
% 7.49/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.49/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3391,plain,
% 7.49/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 7.49/1.50      | r2_hidden(sK3(X0,X2),X0) = iProver_top
% 7.49/1.50      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2313,c_2301]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5757,plain,
% 7.49/1.50      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
% 7.49/1.50      | r2_hidden(sK3(X0,k1_xboole_0),X0) = iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2314,c_3391]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3429,plain,
% 7.49/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.49/1.50      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2313,c_2305]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4792,plain,
% 7.49/1.50      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2314,c_3429]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5760,plain,
% 7.49/1.50      ( k1_relat_1(k1_xboole_0) = X0
% 7.49/1.50      | r2_hidden(sK3(X0,k1_xboole_0),X0) = iProver_top ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_5757,c_4792]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_5765,plain,
% 7.49/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.49/1.50      | r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_5760]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3204,plain,
% 7.49/1.50      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_1700]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_3734,plain,
% 7.49/1.50      ( k1_relat_1(sK7) != X0 | k1_relat_1(sK7) = sK5 | sK5 != X0 ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_3204]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6010,plain,
% 7.49/1.50      ( k1_relat_1(sK7) != k1_relat_1(X0)
% 7.49/1.50      | k1_relat_1(sK7) = sK5
% 7.49/1.50      | sK5 != k1_relat_1(X0) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_3734]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_6011,plain,
% 7.49/1.50      ( k1_relat_1(sK7) != k1_relat_1(k1_xboole_0)
% 7.49/1.50      | k1_relat_1(sK7) = sK5
% 7.49/1.50      | sK5 != k1_relat_1(k1_xboole_0) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_6010]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_2921,plain,
% 7.49/1.50      ( ~ r2_hidden(sK3(X0,X1),X0)
% 7.49/1.50      | r2_hidden(sK3(X0,X1),X2)
% 7.49/1.50      | ~ r1_tarski(X0,X2) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_10470,plain,
% 7.49/1.50      ( ~ r2_hidden(sK3(X0,X1),X0)
% 7.49/1.50      | r2_hidden(sK3(X0,X1),k1_relat_1(X2))
% 7.49/1.50      | ~ r1_tarski(X0,k1_relat_1(X2)) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_2921]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_10475,plain,
% 7.49/1.50      ( r2_hidden(sK3(X0,X1),X0) != iProver_top
% 7.49/1.50      | r2_hidden(sK3(X0,X1),k1_relat_1(X2)) = iProver_top
% 7.49/1.50      | r1_tarski(X0,k1_relat_1(X2)) != iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_10470]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_10477,plain,
% 7.49/1.50      ( r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.49/1.50      | r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top
% 7.49/1.50      | r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_10475]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_4468,plain,
% 7.49/1.50      ( k1_relset_1(X0,X1,sK7) = X0
% 7.49/1.50      | r2_hidden(sK3(X0,sK7),k1_relat_1(sK7)) != iProver_top
% 7.49/1.50      | r1_tarski(sK7,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2313,c_3672]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18962,plain,
% 7.49/1.50      ( k1_relset_1(X0,X1,k1_xboole_0) = X0
% 7.49/1.50      | r2_hidden(sK3(X0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top
% 7.49/1.50      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_18854,c_4468]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_18990,plain,
% 7.49/1.50      ( k1_relat_1(k1_xboole_0) = X0
% 7.49/1.50      | r2_hidden(sK3(X0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top
% 7.49/1.50      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.49/1.50      inference(demodulation,[status(thm)],[c_18962,c_4792]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_19279,plain,
% 7.49/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 7.49/1.50      | r2_hidden(sK3(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) != iProver_top
% 7.49/1.50      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_18990]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20488,plain,
% 7.49/1.50      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20489,plain,
% 7.49/1.50      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.49/1.50      inference(predicate_to_equality,[status(thm)],[c_20488]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_20491,plain,
% 7.49/1.50      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.49/1.50      inference(instantiation,[status(thm)],[c_20489]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_22368,plain,
% 7.49/1.50      ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 7.49/1.50      inference(global_propositional_subsumption,
% 7.49/1.50                [status(thm)],
% 7.49/1.50                [c_18899,c_34,c_654,c_1724,c_2474,c_3194,c_3516,c_3521,
% 7.49/1.50                 c_3553,c_3554,c_3644,c_3742,c_3972,c_4125,c_4440,c_4448,
% 7.49/1.50                 c_5538,c_5547,c_5552,c_5765,c_5840,c_6011,c_6555,c_6635,
% 7.49/1.50                 c_8288,c_10477,c_19279,c_20491]) ).
% 7.49/1.50  
% 7.49/1.50  cnf(c_22372,plain,
% 7.49/1.50      ( $false ),
% 7.49/1.50      inference(superposition,[status(thm)],[c_2314,c_22368]) ).
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.50  
% 7.49/1.50  ------                               Statistics
% 7.49/1.50  
% 7.49/1.50  ------ General
% 7.49/1.50  
% 7.49/1.50  abstr_ref_over_cycles:                  0
% 7.49/1.50  abstr_ref_under_cycles:                 0
% 7.49/1.50  gc_basic_clause_elim:                   0
% 7.49/1.50  forced_gc_time:                         0
% 7.49/1.50  parsing_time:                           0.01
% 7.49/1.50  unif_index_cands_time:                  0.
% 7.49/1.50  unif_index_add_time:                    0.
% 7.49/1.50  orderings_time:                         0.
% 7.49/1.50  out_proof_time:                         0.013
% 7.49/1.50  total_time:                             0.719
% 7.49/1.50  num_of_symbols:                         55
% 7.49/1.50  num_of_terms:                           25687
% 7.49/1.50  
% 7.49/1.50  ------ Preprocessing
% 7.49/1.50  
% 7.49/1.50  num_of_splits:                          0
% 7.49/1.50  num_of_split_atoms:                     0
% 7.49/1.50  num_of_reused_defs:                     0
% 7.49/1.50  num_eq_ax_congr_red:                    42
% 7.49/1.50  num_of_sem_filtered_clauses:            1
% 7.49/1.50  num_of_subtypes:                        0
% 7.49/1.50  monotx_restored_types:                  0
% 7.49/1.50  sat_num_of_epr_types:                   0
% 7.49/1.50  sat_num_of_non_cyclic_types:            0
% 7.49/1.50  sat_guarded_non_collapsed_types:        0
% 7.49/1.50  num_pure_diseq_elim:                    0
% 7.49/1.50  simp_replaced_by:                       0
% 7.49/1.50  res_preprocessed:                       140
% 7.49/1.50  prep_upred:                             0
% 7.49/1.50  prep_unflattend:                        84
% 7.49/1.50  smt_new_axioms:                         0
% 7.49/1.50  pred_elim_cands:                        4
% 7.49/1.50  pred_elim:                              2
% 7.49/1.50  pred_elim_cl:                           5
% 7.49/1.50  pred_elim_cycles:                       6
% 7.49/1.50  merged_defs:                            8
% 7.49/1.50  merged_defs_ncl:                        0
% 7.49/1.50  bin_hyper_res:                          9
% 7.49/1.50  prep_cycles:                            4
% 7.49/1.50  pred_elim_time:                         0.017
% 7.49/1.50  splitting_time:                         0.
% 7.49/1.50  sem_filter_time:                        0.
% 7.49/1.50  monotx_time:                            0.
% 7.49/1.50  subtype_inf_time:                       0.
% 7.49/1.50  
% 7.49/1.50  ------ Problem properties
% 7.49/1.50  
% 7.49/1.50  clauses:                                27
% 7.49/1.50  conjectures:                            3
% 7.49/1.50  epr:                                    3
% 7.49/1.50  horn:                                   23
% 7.49/1.50  ground:                                 5
% 7.49/1.50  unary:                                  4
% 7.49/1.50  binary:                                 8
% 7.49/1.50  lits:                                   69
% 7.49/1.50  lits_eq:                                14
% 7.49/1.50  fd_pure:                                0
% 7.49/1.50  fd_pseudo:                              0
% 7.49/1.50  fd_cond:                                0
% 7.49/1.50  fd_pseudo_cond:                         1
% 7.49/1.50  ac_symbols:                             0
% 7.49/1.50  
% 7.49/1.50  ------ Propositional Solver
% 7.49/1.50  
% 7.49/1.50  prop_solver_calls:                      30
% 7.49/1.50  prop_fast_solver_calls:                 1920
% 7.49/1.50  smt_solver_calls:                       0
% 7.49/1.50  smt_fast_solver_calls:                  0
% 7.49/1.50  prop_num_of_clauses:                    10771
% 7.49/1.50  prop_preprocess_simplified:             16774
% 7.49/1.50  prop_fo_subsumed:                       83
% 7.49/1.50  prop_solver_time:                       0.
% 7.49/1.50  smt_solver_time:                        0.
% 7.49/1.50  smt_fast_solver_time:                   0.
% 7.49/1.50  prop_fast_solver_time:                  0.
% 7.49/1.50  prop_unsat_core_time:                   0.
% 7.49/1.50  
% 7.49/1.50  ------ QBF
% 7.49/1.50  
% 7.49/1.50  qbf_q_res:                              0
% 7.49/1.50  qbf_num_tautologies:                    0
% 7.49/1.50  qbf_prep_cycles:                        0
% 7.49/1.50  
% 7.49/1.50  ------ BMC1
% 7.49/1.50  
% 7.49/1.50  bmc1_current_bound:                     -1
% 7.49/1.50  bmc1_last_solved_bound:                 -1
% 7.49/1.50  bmc1_unsat_core_size:                   -1
% 7.49/1.50  bmc1_unsat_core_parents_size:           -1
% 7.49/1.50  bmc1_merge_next_fun:                    0
% 7.49/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.49/1.50  
% 7.49/1.50  ------ Instantiation
% 7.49/1.50  
% 7.49/1.50  inst_num_of_clauses:                    1999
% 7.49/1.50  inst_num_in_passive:                    515
% 7.49/1.50  inst_num_in_active:                     928
% 7.49/1.50  inst_num_in_unprocessed:                556
% 7.49/1.50  inst_num_of_loops:                      1250
% 7.49/1.50  inst_num_of_learning_restarts:          0
% 7.49/1.50  inst_num_moves_active_passive:          321
% 7.49/1.50  inst_lit_activity:                      0
% 7.49/1.50  inst_lit_activity_moves:                0
% 7.49/1.50  inst_num_tautologies:                   0
% 7.49/1.50  inst_num_prop_implied:                  0
% 7.49/1.50  inst_num_existing_simplified:           0
% 7.49/1.50  inst_num_eq_res_simplified:             0
% 7.49/1.50  inst_num_child_elim:                    0
% 7.49/1.50  inst_num_of_dismatching_blockings:      1826
% 7.49/1.50  inst_num_of_non_proper_insts:           2457
% 7.49/1.50  inst_num_of_duplicates:                 0
% 7.49/1.50  inst_inst_num_from_inst_to_res:         0
% 7.49/1.50  inst_dismatching_checking_time:         0.
% 7.49/1.50  
% 7.49/1.50  ------ Resolution
% 7.49/1.50  
% 7.49/1.50  res_num_of_clauses:                     0
% 7.49/1.50  res_num_in_passive:                     0
% 7.49/1.50  res_num_in_active:                      0
% 7.49/1.50  res_num_of_loops:                       144
% 7.49/1.50  res_forward_subset_subsumed:            53
% 7.49/1.50  res_backward_subset_subsumed:           0
% 7.49/1.50  res_forward_subsumed:                   0
% 7.49/1.50  res_backward_subsumed:                  0
% 7.49/1.50  res_forward_subsumption_resolution:     0
% 7.49/1.50  res_backward_subsumption_resolution:    1
% 7.49/1.50  res_clause_to_clause_subsumption:       5221
% 7.49/1.50  res_orphan_elimination:                 0
% 7.49/1.50  res_tautology_del:                      305
% 7.49/1.50  res_num_eq_res_simplified:              0
% 7.49/1.50  res_num_sel_changes:                    0
% 7.49/1.50  res_moves_from_active_to_pass:          0
% 7.49/1.50  
% 7.49/1.50  ------ Superposition
% 7.49/1.50  
% 7.49/1.50  sup_time_total:                         0.
% 7.49/1.50  sup_time_generating:                    0.
% 7.49/1.50  sup_time_sim_full:                      0.
% 7.49/1.50  sup_time_sim_immed:                     0.
% 7.49/1.50  
% 7.49/1.50  sup_num_of_clauses:                     996
% 7.49/1.50  sup_num_in_active:                      89
% 7.49/1.50  sup_num_in_passive:                     907
% 7.49/1.50  sup_num_of_loops:                       249
% 7.49/1.50  sup_fw_superposition:                   932
% 7.49/1.50  sup_bw_superposition:                   552
% 7.49/1.50  sup_immediate_simplified:               293
% 7.49/1.50  sup_given_eliminated:                   2
% 7.49/1.50  comparisons_done:                       0
% 7.49/1.50  comparisons_avoided:                    6
% 7.49/1.50  
% 7.49/1.50  ------ Simplifications
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  sim_fw_subset_subsumed:                 124
% 7.49/1.50  sim_bw_subset_subsumed:                 59
% 7.49/1.50  sim_fw_subsumed:                        73
% 7.49/1.50  sim_bw_subsumed:                        72
% 7.49/1.50  sim_fw_subsumption_res:                 0
% 7.49/1.50  sim_bw_subsumption_res:                 0
% 7.49/1.50  sim_tautology_del:                      22
% 7.49/1.50  sim_eq_tautology_del:                   10
% 7.49/1.50  sim_eq_res_simp:                        1
% 7.49/1.50  sim_fw_demodulated:                     15
% 7.49/1.50  sim_bw_demodulated:                     142
% 7.49/1.50  sim_light_normalised:                   27
% 7.49/1.50  sim_joinable_taut:                      0
% 7.49/1.50  sim_joinable_simp:                      0
% 7.49/1.50  sim_ac_normalised:                      0
% 7.49/1.50  sim_smt_subsumption:                    0
% 7.49/1.50  
%------------------------------------------------------------------------------
