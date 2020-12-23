%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:59 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  120 (1819 expanded)
%              Number of clauses        :   84 ( 647 expanded)
%              Number of leaves         :   14 ( 448 expanded)
%              Depth                    :   25
%              Number of atoms          :  437 (11168 expanded)
%              Number of equality atoms :  238 (4089 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f21,plain,(
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

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
          & r2_hidden(X3,sK2)
          & r2_hidden(X2,sK2) )
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( sK4 != sK5
    & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK4,sK2)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f21,f20])).

fof(f37,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f11])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
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

fof(f7,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f23,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f31])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_213,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_214,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_442,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X0
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_214])).

cnf(c_443,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_500,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_443])).

cnf(c_555,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_249,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_250,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_560,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_250])).

cnf(c_781,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_560])).

cnf(c_846,plain,
    ( k1_relat_1(sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_555,c_781])).

cnf(c_14,negated_conjecture,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_563,negated_conjecture,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_376,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_377,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_381,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ r2_hidden(X0,k1_relat_1(sK3))
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_17])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | X0 = X1
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_381])).

cnf(c_558,plain,
    ( ~ r2_hidden(X0_49,k1_relat_1(sK3))
    | ~ r2_hidden(X1_49,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49 ),
    inference(subtyping,[status(esa)],[c_382])).

cnf(c_685,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_601,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_567,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_745,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_258,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_259,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_559,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_747,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_748,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_909,plain,
    ( r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | X0_49 = X1_49
    | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_601,c_745,c_748])).

cnf(c_910,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
    | X0_49 = X1_49
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_909])).

cnf(c_917,plain,
    ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,sK4)
    | sK5 = X0_49
    | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_563,c_910])).

cnf(c_937,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_917])).

cnf(c_569,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_593,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_13,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_564,negated_conjecture,
    ( sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_573,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_759,plain,
    ( sK5 != X0_49
    | sK4 != X0_49
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_760,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_964,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_937,c_593,c_564,c_760])).

cnf(c_970,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_964])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_578,plain,
    ( ~ r2_hidden(X0_49,X0_46)
    | r2_hidden(X1_49,X1_46)
    | X1_49 != X0_49
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_761,plain,
    ( r2_hidden(X0_49,X0_46)
    | ~ r2_hidden(sK5,sK2)
    | X0_49 != sK5
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_776,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK2)
    | sK5 != sK5
    | k1_relat_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_814,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_971,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,sK2)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_970])).

cnf(c_973,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_970,c_16,c_15,c_776,c_814,c_846,c_971])).

cnf(c_977,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_973,c_781])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_305,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_306,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_467,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X0
    | sK2 != k1_xboole_0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_306])).

cnf(c_468,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_556,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_468])).

cnf(c_979,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_973,c_556])).

cnf(c_991,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_979])).

cnf(c_994,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_977,c_991])).

cnf(c_562,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_682,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_982,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_973,c_682])).

cnf(c_1003,plain,
    ( r2_hidden(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_982])).

cnf(c_944,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | sK5 = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_937])).

cnf(c_866,plain,
    ( ~ r2_hidden(X0_49,X0_46)
    | r2_hidden(sK4,k1_relat_1(sK3))
    | sK4 != X0_49
    | k1_relat_1(sK3) != X0_46 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_868,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_808,plain,
    ( ~ r2_hidden(X0_49,X0_46)
    | r2_hidden(sK5,k1_relat_1(sK3))
    | sK5 != X0_49
    | k1_relat_1(sK3) != X0_46 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_855,plain,
    ( ~ r2_hidden(sK5,X0_46)
    | r2_hidden(sK5,k1_relat_1(sK3))
    | sK5 != sK5
    | k1_relat_1(sK3) != X0_46 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_858,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,k1_xboole_0)
    | sK5 != sK5
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_571,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_834,plain,
    ( sK2 != X0_46
    | k1_xboole_0 != X0_46
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_835,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_764,plain,
    ( r2_hidden(X0_49,X0_46)
    | ~ r2_hidden(sK4,sK2)
    | X0_49 != sK4
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_766,plain,
    ( ~ r2_hidden(sK4,sK2)
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_566,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_590,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_994,c_1003,c_973,c_944,c_868,c_858,c_835,c_814,c_766,c_760,c_564,c_593,c_590,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.32/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.32/1.03  
% 1.32/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.32/1.03  
% 1.32/1.03  ------  iProver source info
% 1.32/1.03  
% 1.32/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.32/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.32/1.03  git: non_committed_changes: false
% 1.32/1.03  git: last_make_outside_of_git: false
% 1.32/1.03  
% 1.32/1.03  ------ 
% 1.32/1.03  
% 1.32/1.03  ------ Input Options
% 1.32/1.03  
% 1.32/1.03  --out_options                           all
% 1.32/1.03  --tptp_safe_out                         true
% 1.32/1.03  --problem_path                          ""
% 1.32/1.03  --include_path                          ""
% 1.32/1.03  --clausifier                            res/vclausify_rel
% 1.32/1.03  --clausifier_options                    --mode clausify
% 1.32/1.03  --stdin                                 false
% 1.32/1.03  --stats_out                             all
% 1.32/1.03  
% 1.32/1.03  ------ General Options
% 1.32/1.03  
% 1.32/1.03  --fof                                   false
% 1.32/1.03  --time_out_real                         305.
% 1.32/1.03  --time_out_virtual                      -1.
% 1.32/1.03  --symbol_type_check                     false
% 1.32/1.03  --clausify_out                          false
% 1.32/1.03  --sig_cnt_out                           false
% 1.32/1.03  --trig_cnt_out                          false
% 1.32/1.03  --trig_cnt_out_tolerance                1.
% 1.32/1.03  --trig_cnt_out_sk_spl                   false
% 1.32/1.03  --abstr_cl_out                          false
% 1.32/1.03  
% 1.32/1.03  ------ Global Options
% 1.32/1.03  
% 1.32/1.03  --schedule                              default
% 1.32/1.03  --add_important_lit                     false
% 1.32/1.03  --prop_solver_per_cl                    1000
% 1.32/1.03  --min_unsat_core                        false
% 1.32/1.03  --soft_assumptions                      false
% 1.32/1.03  --soft_lemma_size                       3
% 1.32/1.03  --prop_impl_unit_size                   0
% 1.32/1.03  --prop_impl_unit                        []
% 1.32/1.03  --share_sel_clauses                     true
% 1.32/1.03  --reset_solvers                         false
% 1.32/1.03  --bc_imp_inh                            [conj_cone]
% 1.32/1.03  --conj_cone_tolerance                   3.
% 1.32/1.03  --extra_neg_conj                        none
% 1.32/1.03  --large_theory_mode                     true
% 1.32/1.03  --prolific_symb_bound                   200
% 1.32/1.03  --lt_threshold                          2000
% 1.32/1.03  --clause_weak_htbl                      true
% 1.32/1.03  --gc_record_bc_elim                     false
% 1.32/1.03  
% 1.32/1.03  ------ Preprocessing Options
% 1.32/1.03  
% 1.32/1.03  --preprocessing_flag                    true
% 1.32/1.03  --time_out_prep_mult                    0.1
% 1.32/1.03  --splitting_mode                        input
% 1.32/1.03  --splitting_grd                         true
% 1.32/1.03  --splitting_cvd                         false
% 1.32/1.03  --splitting_cvd_svl                     false
% 1.32/1.03  --splitting_nvd                         32
% 1.32/1.03  --sub_typing                            true
% 1.32/1.03  --prep_gs_sim                           true
% 1.32/1.03  --prep_unflatten                        true
% 1.32/1.03  --prep_res_sim                          true
% 1.32/1.03  --prep_upred                            true
% 1.32/1.03  --prep_sem_filter                       exhaustive
% 1.32/1.03  --prep_sem_filter_out                   false
% 1.32/1.03  --pred_elim                             true
% 1.32/1.03  --res_sim_input                         true
% 1.32/1.03  --eq_ax_congr_red                       true
% 1.32/1.03  --pure_diseq_elim                       true
% 1.32/1.03  --brand_transform                       false
% 1.32/1.03  --non_eq_to_eq                          false
% 1.32/1.03  --prep_def_merge                        true
% 1.32/1.03  --prep_def_merge_prop_impl              false
% 1.32/1.03  --prep_def_merge_mbd                    true
% 1.32/1.03  --prep_def_merge_tr_red                 false
% 1.32/1.03  --prep_def_merge_tr_cl                  false
% 1.32/1.03  --smt_preprocessing                     true
% 1.32/1.03  --smt_ac_axioms                         fast
% 1.32/1.03  --preprocessed_out                      false
% 1.32/1.03  --preprocessed_stats                    false
% 1.32/1.03  
% 1.32/1.03  ------ Abstraction refinement Options
% 1.32/1.03  
% 1.32/1.03  --abstr_ref                             []
% 1.32/1.03  --abstr_ref_prep                        false
% 1.32/1.03  --abstr_ref_until_sat                   false
% 1.32/1.03  --abstr_ref_sig_restrict                funpre
% 1.32/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.32/1.03  --abstr_ref_under                       []
% 1.32/1.03  
% 1.32/1.03  ------ SAT Options
% 1.32/1.03  
% 1.32/1.03  --sat_mode                              false
% 1.32/1.03  --sat_fm_restart_options                ""
% 1.32/1.03  --sat_gr_def                            false
% 1.32/1.03  --sat_epr_types                         true
% 1.32/1.03  --sat_non_cyclic_types                  false
% 1.32/1.03  --sat_finite_models                     false
% 1.32/1.03  --sat_fm_lemmas                         false
% 1.32/1.03  --sat_fm_prep                           false
% 1.32/1.03  --sat_fm_uc_incr                        true
% 1.32/1.03  --sat_out_model                         small
% 1.32/1.03  --sat_out_clauses                       false
% 1.32/1.03  
% 1.32/1.03  ------ QBF Options
% 1.32/1.03  
% 1.32/1.03  --qbf_mode                              false
% 1.32/1.03  --qbf_elim_univ                         false
% 1.32/1.03  --qbf_dom_inst                          none
% 1.32/1.03  --qbf_dom_pre_inst                      false
% 1.32/1.03  --qbf_sk_in                             false
% 1.32/1.03  --qbf_pred_elim                         true
% 1.32/1.03  --qbf_split                             512
% 1.32/1.03  
% 1.32/1.03  ------ BMC1 Options
% 1.32/1.03  
% 1.32/1.03  --bmc1_incremental                      false
% 1.32/1.03  --bmc1_axioms                           reachable_all
% 1.32/1.03  --bmc1_min_bound                        0
% 1.32/1.03  --bmc1_max_bound                        -1
% 1.32/1.03  --bmc1_max_bound_default                -1
% 1.32/1.03  --bmc1_symbol_reachability              true
% 1.32/1.03  --bmc1_property_lemmas                  false
% 1.32/1.03  --bmc1_k_induction                      false
% 1.32/1.03  --bmc1_non_equiv_states                 false
% 1.32/1.03  --bmc1_deadlock                         false
% 1.32/1.03  --bmc1_ucm                              false
% 1.32/1.03  --bmc1_add_unsat_core                   none
% 1.32/1.03  --bmc1_unsat_core_children              false
% 1.32/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.32/1.03  --bmc1_out_stat                         full
% 1.32/1.03  --bmc1_ground_init                      false
% 1.32/1.03  --bmc1_pre_inst_next_state              false
% 1.32/1.03  --bmc1_pre_inst_state                   false
% 1.32/1.03  --bmc1_pre_inst_reach_state             false
% 1.32/1.03  --bmc1_out_unsat_core                   false
% 1.32/1.03  --bmc1_aig_witness_out                  false
% 1.32/1.03  --bmc1_verbose                          false
% 1.32/1.03  --bmc1_dump_clauses_tptp                false
% 1.32/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.32/1.03  --bmc1_dump_file                        -
% 1.32/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.32/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.32/1.03  --bmc1_ucm_extend_mode                  1
% 1.32/1.03  --bmc1_ucm_init_mode                    2
% 1.32/1.03  --bmc1_ucm_cone_mode                    none
% 1.32/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.32/1.03  --bmc1_ucm_relax_model                  4
% 1.32/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.32/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.32/1.03  --bmc1_ucm_layered_model                none
% 1.32/1.03  --bmc1_ucm_max_lemma_size               10
% 1.32/1.03  
% 1.32/1.03  ------ AIG Options
% 1.32/1.03  
% 1.32/1.03  --aig_mode                              false
% 1.32/1.03  
% 1.32/1.03  ------ Instantiation Options
% 1.32/1.03  
% 1.32/1.03  --instantiation_flag                    true
% 1.32/1.03  --inst_sos_flag                         false
% 1.32/1.03  --inst_sos_phase                        true
% 1.32/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.32/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.32/1.03  --inst_lit_sel_side                     num_symb
% 1.32/1.03  --inst_solver_per_active                1400
% 1.32/1.03  --inst_solver_calls_frac                1.
% 1.32/1.03  --inst_passive_queue_type               priority_queues
% 1.32/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.32/1.03  --inst_passive_queues_freq              [25;2]
% 1.32/1.03  --inst_dismatching                      true
% 1.32/1.03  --inst_eager_unprocessed_to_passive     true
% 1.32/1.03  --inst_prop_sim_given                   true
% 1.32/1.03  --inst_prop_sim_new                     false
% 1.32/1.03  --inst_subs_new                         false
% 1.32/1.03  --inst_eq_res_simp                      false
% 1.32/1.03  --inst_subs_given                       false
% 1.32/1.03  --inst_orphan_elimination               true
% 1.32/1.03  --inst_learning_loop_flag               true
% 1.32/1.03  --inst_learning_start                   3000
% 1.32/1.03  --inst_learning_factor                  2
% 1.32/1.03  --inst_start_prop_sim_after_learn       3
% 1.32/1.03  --inst_sel_renew                        solver
% 1.32/1.03  --inst_lit_activity_flag                true
% 1.32/1.03  --inst_restr_to_given                   false
% 1.32/1.03  --inst_activity_threshold               500
% 1.32/1.03  --inst_out_proof                        true
% 1.32/1.03  
% 1.32/1.03  ------ Resolution Options
% 1.32/1.03  
% 1.32/1.03  --resolution_flag                       true
% 1.32/1.03  --res_lit_sel                           adaptive
% 1.32/1.03  --res_lit_sel_side                      none
% 1.32/1.03  --res_ordering                          kbo
% 1.32/1.03  --res_to_prop_solver                    active
% 1.32/1.03  --res_prop_simpl_new                    false
% 1.32/1.03  --res_prop_simpl_given                  true
% 1.32/1.03  --res_passive_queue_type                priority_queues
% 1.32/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.32/1.03  --res_passive_queues_freq               [15;5]
% 1.32/1.03  --res_forward_subs                      full
% 1.32/1.03  --res_backward_subs                     full
% 1.32/1.03  --res_forward_subs_resolution           true
% 1.32/1.03  --res_backward_subs_resolution          true
% 1.32/1.03  --res_orphan_elimination                true
% 1.32/1.03  --res_time_limit                        2.
% 1.32/1.03  --res_out_proof                         true
% 1.32/1.03  
% 1.32/1.03  ------ Superposition Options
% 1.32/1.03  
% 1.32/1.03  --superposition_flag                    true
% 1.32/1.03  --sup_passive_queue_type                priority_queues
% 1.32/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.32/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.32/1.03  --demod_completeness_check              fast
% 1.32/1.03  --demod_use_ground                      true
% 1.32/1.03  --sup_to_prop_solver                    passive
% 1.32/1.03  --sup_prop_simpl_new                    true
% 1.32/1.03  --sup_prop_simpl_given                  true
% 1.32/1.03  --sup_fun_splitting                     false
% 1.32/1.03  --sup_smt_interval                      50000
% 1.32/1.03  
% 1.32/1.03  ------ Superposition Simplification Setup
% 1.32/1.03  
% 1.32/1.03  --sup_indices_passive                   []
% 1.32/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.32/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.03  --sup_full_bw                           [BwDemod]
% 1.32/1.03  --sup_immed_triv                        [TrivRules]
% 1.32/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.32/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.03  --sup_immed_bw_main                     []
% 1.32/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.32/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.03  
% 1.32/1.03  ------ Combination Options
% 1.32/1.03  
% 1.32/1.03  --comb_res_mult                         3
% 1.32/1.03  --comb_sup_mult                         2
% 1.32/1.03  --comb_inst_mult                        10
% 1.32/1.03  
% 1.32/1.03  ------ Debug Options
% 1.32/1.03  
% 1.32/1.03  --dbg_backtrace                         false
% 1.32/1.03  --dbg_dump_prop_clauses                 false
% 1.32/1.03  --dbg_dump_prop_clauses_file            -
% 1.32/1.03  --dbg_out_stat                          false
% 1.32/1.03  ------ Parsing...
% 1.32/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.32/1.03  
% 1.32/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.32/1.03  
% 1.32/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.32/1.03  
% 1.32/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.32/1.03  ------ Proving...
% 1.32/1.03  ------ Problem Properties 
% 1.32/1.03  
% 1.32/1.03  
% 1.32/1.03  clauses                                 10
% 1.32/1.03  conjectures                             4
% 1.32/1.03  EPR                                     3
% 1.32/1.03  Horn                                    8
% 1.32/1.03  unary                                   4
% 1.32/1.03  binary                                  3
% 1.32/1.03  lits                                    22
% 1.32/1.03  lits eq                                 16
% 1.32/1.03  fd_pure                                 0
% 1.32/1.03  fd_pseudo                               0
% 1.32/1.03  fd_cond                                 0
% 1.32/1.03  fd_pseudo_cond                          1
% 1.32/1.03  AC symbols                              0
% 1.32/1.03  
% 1.32/1.03  ------ Schedule dynamic 5 is on 
% 1.32/1.03  
% 1.32/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.32/1.03  
% 1.32/1.03  
% 1.32/1.03  ------ 
% 1.32/1.03  Current options:
% 1.32/1.03  ------ 
% 1.32/1.03  
% 1.32/1.03  ------ Input Options
% 1.32/1.03  
% 1.32/1.03  --out_options                           all
% 1.32/1.03  --tptp_safe_out                         true
% 1.32/1.03  --problem_path                          ""
% 1.32/1.03  --include_path                          ""
% 1.32/1.03  --clausifier                            res/vclausify_rel
% 1.32/1.03  --clausifier_options                    --mode clausify
% 1.32/1.03  --stdin                                 false
% 1.32/1.03  --stats_out                             all
% 1.32/1.03  
% 1.32/1.03  ------ General Options
% 1.32/1.03  
% 1.32/1.03  --fof                                   false
% 1.32/1.03  --time_out_real                         305.
% 1.32/1.03  --time_out_virtual                      -1.
% 1.32/1.03  --symbol_type_check                     false
% 1.32/1.03  --clausify_out                          false
% 1.32/1.03  --sig_cnt_out                           false
% 1.32/1.03  --trig_cnt_out                          false
% 1.32/1.03  --trig_cnt_out_tolerance                1.
% 1.32/1.03  --trig_cnt_out_sk_spl                   false
% 1.32/1.03  --abstr_cl_out                          false
% 1.32/1.03  
% 1.32/1.03  ------ Global Options
% 1.32/1.03  
% 1.32/1.03  --schedule                              default
% 1.32/1.03  --add_important_lit                     false
% 1.32/1.03  --prop_solver_per_cl                    1000
% 1.32/1.03  --min_unsat_core                        false
% 1.32/1.03  --soft_assumptions                      false
% 1.32/1.03  --soft_lemma_size                       3
% 1.32/1.03  --prop_impl_unit_size                   0
% 1.32/1.03  --prop_impl_unit                        []
% 1.32/1.03  --share_sel_clauses                     true
% 1.32/1.03  --reset_solvers                         false
% 1.32/1.03  --bc_imp_inh                            [conj_cone]
% 1.32/1.03  --conj_cone_tolerance                   3.
% 1.32/1.03  --extra_neg_conj                        none
% 1.32/1.03  --large_theory_mode                     true
% 1.32/1.03  --prolific_symb_bound                   200
% 1.32/1.03  --lt_threshold                          2000
% 1.32/1.03  --clause_weak_htbl                      true
% 1.32/1.03  --gc_record_bc_elim                     false
% 1.32/1.03  
% 1.32/1.03  ------ Preprocessing Options
% 1.32/1.03  
% 1.32/1.03  --preprocessing_flag                    true
% 1.32/1.03  --time_out_prep_mult                    0.1
% 1.32/1.03  --splitting_mode                        input
% 1.32/1.03  --splitting_grd                         true
% 1.32/1.03  --splitting_cvd                         false
% 1.32/1.03  --splitting_cvd_svl                     false
% 1.32/1.03  --splitting_nvd                         32
% 1.32/1.03  --sub_typing                            true
% 1.32/1.03  --prep_gs_sim                           true
% 1.32/1.03  --prep_unflatten                        true
% 1.32/1.03  --prep_res_sim                          true
% 1.32/1.03  --prep_upred                            true
% 1.32/1.03  --prep_sem_filter                       exhaustive
% 1.32/1.03  --prep_sem_filter_out                   false
% 1.32/1.03  --pred_elim                             true
% 1.32/1.03  --res_sim_input                         true
% 1.32/1.03  --eq_ax_congr_red                       true
% 1.32/1.03  --pure_diseq_elim                       true
% 1.32/1.03  --brand_transform                       false
% 1.32/1.03  --non_eq_to_eq                          false
% 1.32/1.03  --prep_def_merge                        true
% 1.32/1.03  --prep_def_merge_prop_impl              false
% 1.32/1.03  --prep_def_merge_mbd                    true
% 1.32/1.03  --prep_def_merge_tr_red                 false
% 1.32/1.03  --prep_def_merge_tr_cl                  false
% 1.32/1.03  --smt_preprocessing                     true
% 1.32/1.03  --smt_ac_axioms                         fast
% 1.32/1.03  --preprocessed_out                      false
% 1.32/1.03  --preprocessed_stats                    false
% 1.32/1.03  
% 1.32/1.03  ------ Abstraction refinement Options
% 1.32/1.03  
% 1.32/1.03  --abstr_ref                             []
% 1.32/1.03  --abstr_ref_prep                        false
% 1.32/1.03  --abstr_ref_until_sat                   false
% 1.32/1.03  --abstr_ref_sig_restrict                funpre
% 1.32/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.32/1.03  --abstr_ref_under                       []
% 1.32/1.03  
% 1.32/1.03  ------ SAT Options
% 1.32/1.03  
% 1.32/1.03  --sat_mode                              false
% 1.32/1.03  --sat_fm_restart_options                ""
% 1.32/1.03  --sat_gr_def                            false
% 1.32/1.03  --sat_epr_types                         true
% 1.32/1.03  --sat_non_cyclic_types                  false
% 1.32/1.03  --sat_finite_models                     false
% 1.32/1.03  --sat_fm_lemmas                         false
% 1.32/1.03  --sat_fm_prep                           false
% 1.32/1.03  --sat_fm_uc_incr                        true
% 1.32/1.03  --sat_out_model                         small
% 1.32/1.03  --sat_out_clauses                       false
% 1.32/1.03  
% 1.32/1.03  ------ QBF Options
% 1.32/1.03  
% 1.32/1.03  --qbf_mode                              false
% 1.32/1.03  --qbf_elim_univ                         false
% 1.32/1.03  --qbf_dom_inst                          none
% 1.32/1.03  --qbf_dom_pre_inst                      false
% 1.32/1.03  --qbf_sk_in                             false
% 1.32/1.03  --qbf_pred_elim                         true
% 1.32/1.03  --qbf_split                             512
% 1.32/1.03  
% 1.32/1.03  ------ BMC1 Options
% 1.32/1.03  
% 1.32/1.03  --bmc1_incremental                      false
% 1.32/1.03  --bmc1_axioms                           reachable_all
% 1.32/1.03  --bmc1_min_bound                        0
% 1.32/1.03  --bmc1_max_bound                        -1
% 1.32/1.03  --bmc1_max_bound_default                -1
% 1.32/1.03  --bmc1_symbol_reachability              true
% 1.32/1.03  --bmc1_property_lemmas                  false
% 1.32/1.03  --bmc1_k_induction                      false
% 1.32/1.03  --bmc1_non_equiv_states                 false
% 1.32/1.03  --bmc1_deadlock                         false
% 1.32/1.03  --bmc1_ucm                              false
% 1.32/1.03  --bmc1_add_unsat_core                   none
% 1.32/1.03  --bmc1_unsat_core_children              false
% 1.32/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.32/1.03  --bmc1_out_stat                         full
% 1.32/1.03  --bmc1_ground_init                      false
% 1.32/1.03  --bmc1_pre_inst_next_state              false
% 1.32/1.03  --bmc1_pre_inst_state                   false
% 1.32/1.03  --bmc1_pre_inst_reach_state             false
% 1.32/1.03  --bmc1_out_unsat_core                   false
% 1.32/1.03  --bmc1_aig_witness_out                  false
% 1.32/1.03  --bmc1_verbose                          false
% 1.32/1.03  --bmc1_dump_clauses_tptp                false
% 1.32/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.32/1.03  --bmc1_dump_file                        -
% 1.32/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.32/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.32/1.03  --bmc1_ucm_extend_mode                  1
% 1.32/1.03  --bmc1_ucm_init_mode                    2
% 1.32/1.03  --bmc1_ucm_cone_mode                    none
% 1.32/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.32/1.03  --bmc1_ucm_relax_model                  4
% 1.32/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.32/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.32/1.03  --bmc1_ucm_layered_model                none
% 1.32/1.03  --bmc1_ucm_max_lemma_size               10
% 1.32/1.03  
% 1.32/1.03  ------ AIG Options
% 1.32/1.03  
% 1.32/1.03  --aig_mode                              false
% 1.32/1.03  
% 1.32/1.03  ------ Instantiation Options
% 1.32/1.03  
% 1.32/1.03  --instantiation_flag                    true
% 1.32/1.03  --inst_sos_flag                         false
% 1.32/1.03  --inst_sos_phase                        true
% 1.32/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.32/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.32/1.03  --inst_lit_sel_side                     none
% 1.32/1.03  --inst_solver_per_active                1400
% 1.32/1.03  --inst_solver_calls_frac                1.
% 1.32/1.03  --inst_passive_queue_type               priority_queues
% 1.32/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.32/1.03  --inst_passive_queues_freq              [25;2]
% 1.32/1.03  --inst_dismatching                      true
% 1.32/1.03  --inst_eager_unprocessed_to_passive     true
% 1.32/1.03  --inst_prop_sim_given                   true
% 1.32/1.03  --inst_prop_sim_new                     false
% 1.32/1.03  --inst_subs_new                         false
% 1.32/1.03  --inst_eq_res_simp                      false
% 1.32/1.03  --inst_subs_given                       false
% 1.32/1.03  --inst_orphan_elimination               true
% 1.32/1.03  --inst_learning_loop_flag               true
% 1.32/1.03  --inst_learning_start                   3000
% 1.32/1.03  --inst_learning_factor                  2
% 1.32/1.03  --inst_start_prop_sim_after_learn       3
% 1.32/1.03  --inst_sel_renew                        solver
% 1.32/1.03  --inst_lit_activity_flag                true
% 1.32/1.03  --inst_restr_to_given                   false
% 1.32/1.03  --inst_activity_threshold               500
% 1.32/1.03  --inst_out_proof                        true
% 1.32/1.03  
% 1.32/1.03  ------ Resolution Options
% 1.32/1.03  
% 1.32/1.03  --resolution_flag                       false
% 1.32/1.03  --res_lit_sel                           adaptive
% 1.32/1.03  --res_lit_sel_side                      none
% 1.32/1.03  --res_ordering                          kbo
% 1.32/1.03  --res_to_prop_solver                    active
% 1.32/1.03  --res_prop_simpl_new                    false
% 1.32/1.03  --res_prop_simpl_given                  true
% 1.32/1.03  --res_passive_queue_type                priority_queues
% 1.32/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.32/1.03  --res_passive_queues_freq               [15;5]
% 1.32/1.03  --res_forward_subs                      full
% 1.32/1.03  --res_backward_subs                     full
% 1.32/1.03  --res_forward_subs_resolution           true
% 1.32/1.03  --res_backward_subs_resolution          true
% 1.32/1.03  --res_orphan_elimination                true
% 1.32/1.03  --res_time_limit                        2.
% 1.32/1.03  --res_out_proof                         true
% 1.32/1.03  
% 1.32/1.03  ------ Superposition Options
% 1.32/1.03  
% 1.32/1.03  --superposition_flag                    true
% 1.32/1.03  --sup_passive_queue_type                priority_queues
% 1.32/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.32/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.32/1.03  --demod_completeness_check              fast
% 1.32/1.03  --demod_use_ground                      true
% 1.32/1.03  --sup_to_prop_solver                    passive
% 1.32/1.03  --sup_prop_simpl_new                    true
% 1.32/1.03  --sup_prop_simpl_given                  true
% 1.32/1.03  --sup_fun_splitting                     false
% 1.32/1.03  --sup_smt_interval                      50000
% 1.32/1.03  
% 1.32/1.03  ------ Superposition Simplification Setup
% 1.32/1.03  
% 1.32/1.03  --sup_indices_passive                   []
% 1.32/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.32/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.32/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.03  --sup_full_bw                           [BwDemod]
% 1.32/1.03  --sup_immed_triv                        [TrivRules]
% 1.32/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.32/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.03  --sup_immed_bw_main                     []
% 1.32/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.32/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.32/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.32/1.03  
% 1.32/1.03  ------ Combination Options
% 1.32/1.03  
% 1.32/1.03  --comb_res_mult                         3
% 1.32/1.03  --comb_sup_mult                         2
% 1.32/1.03  --comb_inst_mult                        10
% 1.32/1.03  
% 1.32/1.03  ------ Debug Options
% 1.32/1.03  
% 1.32/1.03  --dbg_backtrace                         false
% 1.32/1.03  --dbg_dump_prop_clauses                 false
% 1.32/1.03  --dbg_dump_prop_clauses_file            -
% 1.32/1.03  --dbg_out_stat                          false
% 1.32/1.03  
% 1.32/1.03  
% 1.32/1.03  
% 1.32/1.03  
% 1.32/1.03  ------ Proving...
% 1.32/1.03  
% 1.32/1.03  
% 1.32/1.03  % SZS status Theorem for theBenchmark.p
% 1.32/1.03  
% 1.32/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.32/1.03  
% 1.32/1.03  fof(f5,conjecture,(
% 1.32/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.03  
% 1.32/1.03  fof(f6,negated_conjecture,(
% 1.32/1.03    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.32/1.03    inference(negated_conjecture,[],[f5])).
% 1.32/1.03  
% 1.32/1.03  fof(f13,plain,(
% 1.32/1.03    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.32/1.03    inference(ennf_transformation,[],[f6])).
% 1.32/1.03  
% 1.32/1.03  fof(f14,plain,(
% 1.32/1.03    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.32/1.03    inference(flattening,[],[f13])).
% 1.32/1.03  
% 1.32/1.03  fof(f21,plain,(
% 1.32/1.03    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 1.32/1.03    introduced(choice_axiom,[])).
% 1.32/1.03  
% 1.32/1.03  fof(f20,plain,(
% 1.32/1.03    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 1.32/1.03    introduced(choice_axiom,[])).
% 1.32/1.03  
% 1.32/1.03  fof(f22,plain,(
% 1.32/1.03    (sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 1.32/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f21,f20])).
% 1.32/1.03  
% 1.32/1.03  fof(f37,plain,(
% 1.32/1.03    v1_funct_2(sK3,sK2,sK2)),
% 1.32/1.03    inference(cnf_transformation,[],[f22])).
% 1.32/1.03  
% 1.32/1.03  fof(f4,axiom,(
% 1.32/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.03  
% 1.32/1.03  fof(f11,plain,(
% 1.32/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/1.03    inference(ennf_transformation,[],[f4])).
% 1.32/1.03  
% 1.32/1.03  fof(f12,plain,(
% 1.32/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/1.03    inference(flattening,[],[f11])).
% 1.32/1.03  
% 1.32/1.03  fof(f19,plain,(
% 1.32/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/1.03    inference(nnf_transformation,[],[f12])).
% 1.32/1.03  
% 1.32/1.03  fof(f30,plain,(
% 1.32/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/1.03    inference(cnf_transformation,[],[f19])).
% 1.32/1.03  
% 1.32/1.03  fof(f38,plain,(
% 1.32/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.32/1.03    inference(cnf_transformation,[],[f22])).
% 1.32/1.03  
% 1.32/1.03  fof(f3,axiom,(
% 1.32/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.03  
% 1.32/1.03  fof(f10,plain,(
% 1.32/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/1.03    inference(ennf_transformation,[],[f3])).
% 1.32/1.03  
% 1.32/1.03  fof(f29,plain,(
% 1.32/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/1.03    inference(cnf_transformation,[],[f10])).
% 1.32/1.03  
% 1.32/1.03  fof(f42,plain,(
% 1.32/1.03    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 1.32/1.03    inference(cnf_transformation,[],[f22])).
% 1.32/1.03  
% 1.32/1.03  fof(f1,axiom,(
% 1.32/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.03  
% 1.32/1.03  fof(f7,plain,(
% 1.32/1.03    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.32/1.03    inference(ennf_transformation,[],[f1])).
% 1.32/1.03  
% 1.32/1.03  fof(f8,plain,(
% 1.32/1.03    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/1.03    inference(flattening,[],[f7])).
% 1.32/1.03  
% 1.32/1.03  fof(f15,plain,(
% 1.32/1.03    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/1.03    inference(nnf_transformation,[],[f8])).
% 1.32/1.03  
% 1.32/1.03  fof(f16,plain,(
% 1.32/1.03    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/1.03    inference(rectify,[],[f15])).
% 1.32/1.03  
% 1.32/1.03  fof(f17,plain,(
% 1.32/1.03    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 1.32/1.03    introduced(choice_axiom,[])).
% 1.32/1.03  
% 1.32/1.03  fof(f18,plain,(
% 1.32/1.03    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.32/1.03  
% 1.32/1.03  fof(f23,plain,(
% 1.32/1.03    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/1.03    inference(cnf_transformation,[],[f18])).
% 1.32/1.03  
% 1.32/1.03  fof(f36,plain,(
% 1.32/1.03    v1_funct_1(sK3)),
% 1.32/1.03    inference(cnf_transformation,[],[f22])).
% 1.32/1.03  
% 1.32/1.03  fof(f39,plain,(
% 1.32/1.03    v2_funct_1(sK3)),
% 1.32/1.03    inference(cnf_transformation,[],[f22])).
% 1.32/1.03  
% 1.32/1.03  fof(f2,axiom,(
% 1.32/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.32/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.32/1.03  
% 1.32/1.03  fof(f9,plain,(
% 1.32/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/1.03    inference(ennf_transformation,[],[f2])).
% 1.32/1.03  
% 1.32/1.03  fof(f28,plain,(
% 1.32/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/1.03    inference(cnf_transformation,[],[f9])).
% 1.32/1.03  
% 1.32/1.03  fof(f43,plain,(
% 1.32/1.03    sK4 != sK5),
% 1.32/1.03    inference(cnf_transformation,[],[f22])).
% 1.32/1.03  
% 1.32/1.03  fof(f40,plain,(
% 1.32/1.03    r2_hidden(sK4,sK2)),
% 1.32/1.03    inference(cnf_transformation,[],[f22])).
% 1.32/1.03  
% 1.32/1.03  fof(f41,plain,(
% 1.32/1.03    r2_hidden(sK5,sK2)),
% 1.32/1.03    inference(cnf_transformation,[],[f22])).
% 1.32/1.03  
% 1.32/1.03  fof(f31,plain,(
% 1.32/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/1.03    inference(cnf_transformation,[],[f19])).
% 1.32/1.03  
% 1.32/1.03  fof(f48,plain,(
% 1.32/1.03    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.32/1.03    inference(equality_resolution,[],[f31])).
% 1.32/1.03  
% 1.32/1.03  cnf(c_19,negated_conjecture,
% 1.32/1.03      ( v1_funct_2(sK3,sK2,sK2) ),
% 1.32/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_12,plain,
% 1.32/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.32/1.03      | k1_relset_1(X1,X2,X0) = X1
% 1.32/1.03      | k1_xboole_0 = X2 ),
% 1.32/1.03      inference(cnf_transformation,[],[f30]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_18,negated_conjecture,
% 1.32/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.32/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_213,plain,
% 1.32/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.32/1.03      | k1_relset_1(X1,X2,X0) = X1
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | sK3 != X0
% 1.32/1.03      | k1_xboole_0 = X2 ),
% 1.32/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_214,plain,
% 1.32/1.03      ( ~ v1_funct_2(sK3,X0,X1)
% 1.32/1.03      | k1_relset_1(X0,X1,sK3) = X0
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | k1_xboole_0 = X1 ),
% 1.32/1.03      inference(unflattening,[status(thm)],[c_213]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_442,plain,
% 1.32/1.03      ( k1_relset_1(X0,X1,sK3) = X0
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | sK2 != X0
% 1.32/1.03      | sK2 != X1
% 1.32/1.03      | sK3 != sK3
% 1.32/1.03      | k1_xboole_0 = X1 ),
% 1.32/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_214]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_443,plain,
% 1.32/1.03      ( k1_relset_1(sK2,sK2,sK3) = sK2
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | k1_xboole_0 = sK2 ),
% 1.32/1.03      inference(unflattening,[status(thm)],[c_442]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_500,plain,
% 1.32/1.03      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 1.32/1.03      inference(equality_resolution_simp,[status(thm)],[c_443]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_555,plain,
% 1.32/1.03      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 1.32/1.03      inference(subtyping,[status(esa)],[c_500]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_6,plain,
% 1.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.32/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.32/1.03      inference(cnf_transformation,[],[f29]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_249,plain,
% 1.32/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | sK3 != X2 ),
% 1.32/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_250,plain,
% 1.32/1.03      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.32/1.03      inference(unflattening,[status(thm)],[c_249]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_560,plain,
% 1.32/1.03      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
% 1.32/1.03      inference(subtyping,[status(esa)],[c_250]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_781,plain,
% 1.32/1.03      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 1.32/1.03      inference(equality_resolution,[status(thm)],[c_560]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_846,plain,
% 1.32/1.03      ( k1_relat_1(sK3) = sK2 | sK2 = k1_xboole_0 ),
% 1.32/1.03      inference(demodulation,[status(thm)],[c_555,c_781]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_14,negated_conjecture,
% 1.32/1.03      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.32/1.03      inference(cnf_transformation,[],[f42]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_563,negated_conjecture,
% 1.32/1.03      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.32/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_4,plain,
% 1.32/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.32/1.03      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.32/1.03      | ~ v1_relat_1(X1)
% 1.32/1.03      | ~ v1_funct_1(X1)
% 1.32/1.03      | ~ v2_funct_1(X1)
% 1.32/1.03      | X0 = X2
% 1.32/1.03      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 1.32/1.03      inference(cnf_transformation,[],[f23]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_20,negated_conjecture,
% 1.32/1.03      ( v1_funct_1(sK3) ),
% 1.32/1.03      inference(cnf_transformation,[],[f36]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_376,plain,
% 1.32/1.03      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.32/1.03      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.32/1.03      | ~ v1_relat_1(X1)
% 1.32/1.03      | ~ v2_funct_1(X1)
% 1.32/1.03      | X2 = X0
% 1.32/1.03      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 1.32/1.03      | sK3 != X1 ),
% 1.32/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_377,plain,
% 1.32/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.32/1.03      | ~ v1_relat_1(sK3)
% 1.32/1.03      | ~ v2_funct_1(sK3)
% 1.32/1.03      | X0 = X1
% 1.32/1.03      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 1.32/1.03      inference(unflattening,[status(thm)],[c_376]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_17,negated_conjecture,
% 1.32/1.03      ( v2_funct_1(sK3) ),
% 1.32/1.03      inference(cnf_transformation,[],[f39]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_381,plain,
% 1.32/1.03      ( ~ v1_relat_1(sK3)
% 1.32/1.03      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.32/1.03      | X0 = X1
% 1.32/1.03      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 1.32/1.03      inference(global_propositional_subsumption,
% 1.32/1.03                [status(thm)],
% 1.32/1.03                [c_377,c_17]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_382,plain,
% 1.32/1.03      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.32/1.03      | ~ v1_relat_1(sK3)
% 1.32/1.03      | X0 = X1
% 1.32/1.03      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 1.32/1.03      inference(renaming,[status(thm)],[c_381]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_558,plain,
% 1.32/1.03      ( ~ r2_hidden(X0_49,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(X1_49,k1_relat_1(sK3))
% 1.32/1.03      | ~ v1_relat_1(sK3)
% 1.32/1.03      | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.32/1.03      | X0_49 = X1_49 ),
% 1.32/1.03      inference(subtyping,[status(esa)],[c_382]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_685,plain,
% 1.32/1.03      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.32/1.03      | X0_49 = X1_49
% 1.32/1.03      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.32/1.03      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_601,plain,
% 1.32/1.03      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.32/1.03      | X0_49 = X1_49
% 1.32/1.03      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.32/1.03      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_567,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_745,plain,
% 1.32/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_567]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_5,plain,
% 1.32/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.32/1.03      | v1_relat_1(X0) ),
% 1.32/1.03      inference(cnf_transformation,[],[f28]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_258,plain,
% 1.32/1.03      ( v1_relat_1(X0)
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | sK3 != X0 ),
% 1.32/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_259,plain,
% 1.32/1.03      ( v1_relat_1(sK3)
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.32/1.03      inference(unflattening,[status(thm)],[c_258]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_559,plain,
% 1.32/1.03      ( v1_relat_1(sK3)
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.32/1.03      inference(subtyping,[status(esa)],[c_259]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_747,plain,
% 1.32/1.03      ( v1_relat_1(sK3)
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_559]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_748,plain,
% 1.32/1.03      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | v1_relat_1(sK3) = iProver_top ),
% 1.32/1.03      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_909,plain,
% 1.32/1.03      ( r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | X0_49 = X1_49
% 1.32/1.03      | k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49) ),
% 1.32/1.03      inference(global_propositional_subsumption,
% 1.32/1.03                [status(thm)],
% 1.32/1.03                [c_685,c_601,c_745,c_748]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_910,plain,
% 1.32/1.03      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,X1_49)
% 1.32/1.03      | X0_49 = X1_49
% 1.32/1.03      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | r2_hidden(X1_49,k1_relat_1(sK3)) != iProver_top ),
% 1.32/1.03      inference(renaming,[status(thm)],[c_909]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_917,plain,
% 1.32/1.03      ( k1_funct_1(sK3,X0_49) != k1_funct_1(sK3,sK4)
% 1.32/1.03      | sK5 = X0_49
% 1.32/1.03      | r2_hidden(X0_49,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
% 1.32/1.03      inference(superposition,[status(thm)],[c_563,c_910]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_937,plain,
% 1.32/1.03      ( sK5 = sK4
% 1.32/1.03      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 1.32/1.03      inference(equality_resolution,[status(thm)],[c_917]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_569,plain,( X0_49 = X0_49 ),theory(equality) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_593,plain,
% 1.32/1.03      ( sK4 = sK4 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_569]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_13,negated_conjecture,
% 1.32/1.03      ( sK4 != sK5 ),
% 1.32/1.03      inference(cnf_transformation,[],[f43]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_564,negated_conjecture,
% 1.32/1.03      ( sK4 != sK5 ),
% 1.32/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_573,plain,
% 1.32/1.03      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 1.32/1.03      theory(equality) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_759,plain,
% 1.32/1.03      ( sK5 != X0_49 | sK4 != X0_49 | sK4 = sK5 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_573]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_760,plain,
% 1.32/1.03      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_759]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_964,plain,
% 1.32/1.03      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 1.32/1.03      inference(global_propositional_subsumption,
% 1.32/1.03                [status(thm)],
% 1.32/1.03                [c_937,c_593,c_564,c_760]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_970,plain,
% 1.32/1.03      ( sK2 = k1_xboole_0
% 1.32/1.03      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 1.32/1.03      | r2_hidden(sK4,sK2) != iProver_top ),
% 1.32/1.03      inference(superposition,[status(thm)],[c_846,c_964]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_16,negated_conjecture,
% 1.32/1.03      ( r2_hidden(sK4,sK2) ),
% 1.32/1.03      inference(cnf_transformation,[],[f40]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_15,negated_conjecture,
% 1.32/1.03      ( r2_hidden(sK5,sK2) ),
% 1.32/1.03      inference(cnf_transformation,[],[f41]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_578,plain,
% 1.32/1.03      ( ~ r2_hidden(X0_49,X0_46)
% 1.32/1.03      | r2_hidden(X1_49,X1_46)
% 1.32/1.03      | X1_49 != X0_49
% 1.32/1.03      | X1_46 != X0_46 ),
% 1.32/1.03      theory(equality) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_761,plain,
% 1.32/1.03      ( r2_hidden(X0_49,X0_46)
% 1.32/1.03      | ~ r2_hidden(sK5,sK2)
% 1.32/1.03      | X0_49 != sK5
% 1.32/1.03      | X0_46 != sK2 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_578]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_776,plain,
% 1.32/1.03      ( r2_hidden(sK5,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(sK5,sK2)
% 1.32/1.03      | sK5 != sK5
% 1.32/1.03      | k1_relat_1(sK3) != sK2 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_761]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_814,plain,
% 1.32/1.03      ( sK5 = sK5 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_569]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_971,plain,
% 1.32/1.03      ( ~ r2_hidden(sK5,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(sK4,sK2)
% 1.32/1.03      | sK2 = k1_xboole_0 ),
% 1.32/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_970]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_973,plain,
% 1.32/1.03      ( sK2 = k1_xboole_0 ),
% 1.32/1.03      inference(global_propositional_subsumption,
% 1.32/1.03                [status(thm)],
% 1.32/1.03                [c_970,c_16,c_15,c_776,c_814,c_846,c_971]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_977,plain,
% 1.32/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 1.32/1.03      inference(demodulation,[status(thm)],[c_973,c_781]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_11,plain,
% 1.32/1.03      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.32/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.32/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.32/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_305,plain,
% 1.32/1.03      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.32/1.03      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | sK3 != X0 ),
% 1.32/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_306,plain,
% 1.32/1.03      ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
% 1.32/1.03      | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.32/1.03      inference(unflattening,[status(thm)],[c_305]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_467,plain,
% 1.32/1.03      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | sK2 != X0
% 1.32/1.03      | sK2 != k1_xboole_0
% 1.32/1.03      | sK3 != sK3 ),
% 1.32/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_306]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_468,plain,
% 1.32/1.03      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.32/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | sK2 != k1_xboole_0 ),
% 1.32/1.03      inference(unflattening,[status(thm)],[c_467]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_556,plain,
% 1.32/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.32/1.03      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.32/1.03      | sK2 != k1_xboole_0 ),
% 1.32/1.03      inference(subtyping,[status(esa)],[c_468]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_979,plain,
% 1.32/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.32/1.03      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 1.32/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 1.32/1.03      inference(demodulation,[status(thm)],[c_973,c_556]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_991,plain,
% 1.32/1.03      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 1.32/1.03      inference(equality_resolution_simp,[status(thm)],[c_979]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_994,plain,
% 1.32/1.03      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.32/1.03      inference(light_normalisation,[status(thm)],[c_977,c_991]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_562,negated_conjecture,
% 1.32/1.03      ( r2_hidden(sK5,sK2) ),
% 1.32/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_682,plain,
% 1.32/1.03      ( r2_hidden(sK5,sK2) = iProver_top ),
% 1.32/1.03      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_982,plain,
% 1.32/1.03      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 1.32/1.03      inference(demodulation,[status(thm)],[c_973,c_682]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_1003,plain,
% 1.32/1.03      ( r2_hidden(sK5,k1_xboole_0) ),
% 1.32/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_982]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_944,plain,
% 1.32/1.03      ( ~ r2_hidden(sK5,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(sK4,k1_relat_1(sK3))
% 1.32/1.03      | sK5 = sK4 ),
% 1.32/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_937]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_866,plain,
% 1.32/1.03      ( ~ r2_hidden(X0_49,X0_46)
% 1.32/1.03      | r2_hidden(sK4,k1_relat_1(sK3))
% 1.32/1.03      | sK4 != X0_49
% 1.32/1.03      | k1_relat_1(sK3) != X0_46 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_578]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_868,plain,
% 1.32/1.03      ( r2_hidden(sK4,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(sK4,k1_xboole_0)
% 1.32/1.03      | sK4 != sK4
% 1.32/1.03      | k1_relat_1(sK3) != k1_xboole_0 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_866]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_808,plain,
% 1.32/1.03      ( ~ r2_hidden(X0_49,X0_46)
% 1.32/1.03      | r2_hidden(sK5,k1_relat_1(sK3))
% 1.32/1.03      | sK5 != X0_49
% 1.32/1.03      | k1_relat_1(sK3) != X0_46 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_578]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_855,plain,
% 1.32/1.03      ( ~ r2_hidden(sK5,X0_46)
% 1.32/1.03      | r2_hidden(sK5,k1_relat_1(sK3))
% 1.32/1.03      | sK5 != sK5
% 1.32/1.03      | k1_relat_1(sK3) != X0_46 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_808]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_858,plain,
% 1.32/1.03      ( r2_hidden(sK5,k1_relat_1(sK3))
% 1.32/1.03      | ~ r2_hidden(sK5,k1_xboole_0)
% 1.32/1.03      | sK5 != sK5
% 1.32/1.03      | k1_relat_1(sK3) != k1_xboole_0 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_855]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_571,plain,
% 1.32/1.03      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 1.32/1.03      theory(equality) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_834,plain,
% 1.32/1.03      ( sK2 != X0_46 | k1_xboole_0 != X0_46 | k1_xboole_0 = sK2 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_571]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_835,plain,
% 1.32/1.03      ( sK2 != k1_xboole_0
% 1.32/1.03      | k1_xboole_0 = sK2
% 1.32/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_834]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_764,plain,
% 1.32/1.03      ( r2_hidden(X0_49,X0_46)
% 1.32/1.03      | ~ r2_hidden(sK4,sK2)
% 1.32/1.03      | X0_49 != sK4
% 1.32/1.03      | X0_46 != sK2 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_578]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_766,plain,
% 1.32/1.03      ( ~ r2_hidden(sK4,sK2)
% 1.32/1.03      | r2_hidden(sK4,k1_xboole_0)
% 1.32/1.03      | sK4 != sK4
% 1.32/1.03      | k1_xboole_0 != sK2 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_764]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_566,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.32/1.03  
% 1.32/1.03  cnf(c_590,plain,
% 1.32/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 1.32/1.03      inference(instantiation,[status(thm)],[c_566]) ).
% 1.32/1.03  
% 1.32/1.03  cnf(contradiction,plain,
% 1.32/1.03      ( $false ),
% 1.32/1.03      inference(minisat,
% 1.32/1.03                [status(thm)],
% 1.32/1.03                [c_994,c_1003,c_973,c_944,c_868,c_858,c_835,c_814,c_766,
% 1.32/1.03                 c_760,c_564,c_593,c_590,c_16]) ).
% 1.32/1.03  
% 1.32/1.03  
% 1.32/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.32/1.03  
% 1.32/1.03  ------                               Statistics
% 1.32/1.03  
% 1.32/1.03  ------ General
% 1.32/1.03  
% 1.32/1.03  abstr_ref_over_cycles:                  0
% 1.32/1.03  abstr_ref_under_cycles:                 0
% 1.32/1.03  gc_basic_clause_elim:                   0
% 1.32/1.03  forced_gc_time:                         0
% 1.32/1.03  parsing_time:                           0.012
% 1.32/1.03  unif_index_cands_time:                  0.
% 1.32/1.03  unif_index_add_time:                    0.
% 1.32/1.03  orderings_time:                         0.
% 1.32/1.03  out_proof_time:                         0.037
% 1.32/1.03  total_time:                             0.116
% 1.32/1.03  num_of_symbols:                         51
% 1.32/1.03  num_of_terms:                           987
% 1.32/1.03  
% 1.32/1.03  ------ Preprocessing
% 1.32/1.03  
% 1.32/1.03  num_of_splits:                          0
% 1.32/1.03  num_of_split_atoms:                     0
% 1.32/1.03  num_of_reused_defs:                     0
% 1.32/1.03  num_eq_ax_congr_red:                    6
% 1.32/1.03  num_of_sem_filtered_clauses:            1
% 1.32/1.03  num_of_subtypes:                        5
% 1.32/1.03  monotx_restored_types:                  0
% 1.32/1.03  sat_num_of_epr_types:                   0
% 1.32/1.03  sat_num_of_non_cyclic_types:            0
% 1.32/1.03  sat_guarded_non_collapsed_types:        1
% 1.32/1.03  num_pure_diseq_elim:                    0
% 1.32/1.03  simp_replaced_by:                       0
% 1.32/1.03  res_preprocessed:                       84
% 1.32/1.03  prep_upred:                             0
% 1.32/1.03  prep_unflattend:                        29
% 1.32/1.03  smt_new_axioms:                         0
% 1.32/1.03  pred_elim_cands:                        2
% 1.32/1.03  pred_elim:                              4
% 1.32/1.03  pred_elim_cl:                           11
% 1.32/1.03  pred_elim_cycles:                       7
% 1.32/1.03  merged_defs:                            0
% 1.32/1.03  merged_defs_ncl:                        0
% 1.32/1.03  bin_hyper_res:                          0
% 1.32/1.03  prep_cycles:                            4
% 1.32/1.03  pred_elim_time:                         0.008
% 1.32/1.03  splitting_time:                         0.
% 1.32/1.03  sem_filter_time:                        0.
% 1.32/1.03  monotx_time:                            0.
% 1.32/1.03  subtype_inf_time:                       0.
% 1.32/1.03  
% 1.32/1.03  ------ Problem properties
% 1.32/1.03  
% 1.32/1.03  clauses:                                10
% 1.32/1.03  conjectures:                            4
% 1.32/1.03  epr:                                    3
% 1.32/1.03  horn:                                   8
% 1.32/1.03  ground:                                 7
% 1.32/1.03  unary:                                  4
% 1.32/1.03  binary:                                 3
% 1.32/1.03  lits:                                   22
% 1.32/1.03  lits_eq:                                16
% 1.32/1.03  fd_pure:                                0
% 1.32/1.03  fd_pseudo:                              0
% 1.32/1.03  fd_cond:                                0
% 1.32/1.03  fd_pseudo_cond:                         1
% 1.32/1.03  ac_symbols:                             0
% 1.32/1.03  
% 1.32/1.03  ------ Propositional Solver
% 1.32/1.03  
% 1.32/1.03  prop_solver_calls:                      26
% 1.32/1.03  prop_fast_solver_calls:                 498
% 1.32/1.03  smt_solver_calls:                       0
% 1.32/1.03  smt_fast_solver_calls:                  0
% 1.32/1.03  prop_num_of_clauses:                    260
% 1.32/1.03  prop_preprocess_simplified:             1678
% 1.32/1.03  prop_fo_subsumed:                       6
% 1.32/1.03  prop_solver_time:                       0.
% 1.32/1.03  smt_solver_time:                        0.
% 1.32/1.03  smt_fast_solver_time:                   0.
% 1.32/1.03  prop_fast_solver_time:                  0.
% 1.32/1.03  prop_unsat_core_time:                   0.
% 1.32/1.03  
% 1.32/1.03  ------ QBF
% 1.32/1.03  
% 1.32/1.03  qbf_q_res:                              0
% 1.32/1.03  qbf_num_tautologies:                    0
% 1.32/1.03  qbf_prep_cycles:                        0
% 1.32/1.03  
% 1.32/1.03  ------ BMC1
% 1.32/1.03  
% 1.32/1.03  bmc1_current_bound:                     -1
% 1.32/1.03  bmc1_last_solved_bound:                 -1
% 1.32/1.03  bmc1_unsat_core_size:                   -1
% 1.32/1.03  bmc1_unsat_core_parents_size:           -1
% 1.32/1.03  bmc1_merge_next_fun:                    0
% 1.32/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.32/1.03  
% 1.32/1.03  ------ Instantiation
% 1.32/1.03  
% 1.32/1.03  inst_num_of_clauses:                    68
% 1.32/1.03  inst_num_in_passive:                    10
% 1.32/1.03  inst_num_in_active:                     58
% 1.32/1.03  inst_num_in_unprocessed:                0
% 1.32/1.03  inst_num_of_loops:                      70
% 1.32/1.03  inst_num_of_learning_restarts:          0
% 1.32/1.03  inst_num_moves_active_passive:          9
% 1.32/1.03  inst_lit_activity:                      0
% 1.32/1.03  inst_lit_activity_moves:                0
% 1.32/1.03  inst_num_tautologies:                   0
% 1.32/1.03  inst_num_prop_implied:                  0
% 1.32/1.03  inst_num_existing_simplified:           0
% 1.32/1.03  inst_num_eq_res_simplified:             0
% 1.32/1.03  inst_num_child_elim:                    0
% 1.32/1.03  inst_num_of_dismatching_blockings:      5
% 1.32/1.03  inst_num_of_non_proper_insts:           58
% 1.32/1.03  inst_num_of_duplicates:                 0
% 1.32/1.03  inst_inst_num_from_inst_to_res:         0
% 1.32/1.03  inst_dismatching_checking_time:         0.
% 1.32/1.03  
% 1.32/1.03  ------ Resolution
% 1.32/1.03  
% 1.32/1.03  res_num_of_clauses:                     0
% 1.32/1.03  res_num_in_passive:                     0
% 1.32/1.03  res_num_in_active:                      0
% 1.32/1.03  res_num_of_loops:                       88
% 1.32/1.03  res_forward_subset_subsumed:            12
% 1.32/1.03  res_backward_subset_subsumed:           0
% 1.32/1.03  res_forward_subsumed:                   0
% 1.32/1.03  res_backward_subsumed:                  0
% 1.32/1.03  res_forward_subsumption_resolution:     0
% 1.32/1.03  res_backward_subsumption_resolution:    0
% 1.32/1.03  res_clause_to_clause_subsumption:       21
% 1.32/1.03  res_orphan_elimination:                 0
% 1.32/1.03  res_tautology_del:                      17
% 1.32/1.03  res_num_eq_res_simplified:              1
% 1.32/1.03  res_num_sel_changes:                    0
% 1.32/1.03  res_moves_from_active_to_pass:          0
% 1.32/1.03  
% 1.32/1.03  ------ Superposition
% 1.32/1.03  
% 1.32/1.03  sup_time_total:                         0.
% 1.32/1.03  sup_time_generating:                    0.
% 1.32/1.03  sup_time_sim_full:                      0.
% 1.32/1.03  sup_time_sim_immed:                     0.
% 1.32/1.03  
% 1.32/1.03  sup_num_of_clauses:                     11
% 1.32/1.03  sup_num_in_active:                      6
% 1.32/1.03  sup_num_in_passive:                     5
% 1.32/1.03  sup_num_of_loops:                       13
% 1.32/1.03  sup_fw_superposition:                   4
% 1.32/1.03  sup_bw_superposition:                   0
% 1.32/1.03  sup_immediate_simplified:               2
% 1.32/1.03  sup_given_eliminated:                   0
% 1.32/1.03  comparisons_done:                       0
% 1.32/1.03  comparisons_avoided:                    0
% 1.32/1.03  
% 1.32/1.03  ------ Simplifications
% 1.32/1.03  
% 1.32/1.03  
% 1.32/1.03  sim_fw_subset_subsumed:                 0
% 1.32/1.03  sim_bw_subset_subsumed:                 0
% 1.32/1.03  sim_fw_subsumed:                        0
% 1.32/1.03  sim_bw_subsumed:                        0
% 1.32/1.03  sim_fw_subsumption_res:                 0
% 1.32/1.03  sim_bw_subsumption_res:                 0
% 1.32/1.03  sim_tautology_del:                      1
% 1.32/1.03  sim_eq_tautology_del:                   3
% 1.32/1.03  sim_eq_res_simp:                        1
% 1.32/1.03  sim_fw_demodulated:                     1
% 1.32/1.03  sim_bw_demodulated:                     8
% 1.32/1.03  sim_light_normalised:                   1
% 1.32/1.03  sim_joinable_taut:                      0
% 1.32/1.03  sim_joinable_simp:                      0
% 1.32/1.03  sim_ac_normalised:                      0
% 1.32/1.03  sim_smt_subsumption:                    0
% 1.32/1.03  
%------------------------------------------------------------------------------
