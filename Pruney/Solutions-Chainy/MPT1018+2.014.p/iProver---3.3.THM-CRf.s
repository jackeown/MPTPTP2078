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
% DateTime   : Thu Dec  3 12:07:01 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  123 (1877 expanded)
%              Number of clauses        :   85 ( 687 expanded)
%              Number of leaves         :   15 ( 455 expanded)
%              Depth                    :   26
%              Number of atoms          :  438 (11307 expanded)
%              Number of equality atoms :  239 (4112 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

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
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f22,plain,(
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

fof(f21,plain,
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

fof(f23,plain,
    ( sK4 != sK5
    & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK4,sK2)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f15,f22,f21])).

fof(f39,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f26,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f33])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_237,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_238,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_430,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X0
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_238])).

cnf(c_431,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_489,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_431])).

cnf(c_525,plain,
    ( k1_relset_1(sK2,sK2,sK3) = sK2
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_489])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_273,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_274,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_529,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_274])).

cnf(c_779,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_529])).

cnf(c_834,plain,
    ( k1_relat_1(sK3) = sK2
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_525,c_779])).

cnf(c_15,negated_conjecture,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_533,negated_conjecture,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_381,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_386,plain,
    ( ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_18])).

cnf(c_387,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
    inference(renaming,[status(thm)],[c_386])).

cnf(c_528,plain,
    ( ~ r2_hidden(X0_48,k1_relat_1(sK3))
    | ~ r2_hidden(X1_48,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48)
    | X1_48 = X0_48 ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_667,plain,
    ( k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48)
    | X1_48 = X0_48
    | r2_hidden(X1_48,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_571,plain,
    ( k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48)
    | X1_48 = X0_48
    | r2_hidden(X1_48,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_538,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_738,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_222,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_223,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_530,plain,
    ( ~ v1_relat_1(X0_46)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0_46) ),
    inference(subtyping,[status(esa)],[c_223])).

cnf(c_733,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_46,X1_46))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_793,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_794,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_535,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_820,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_821,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_888,plain,
    ( r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X1_48,k1_relat_1(sK3)) != iProver_top
    | X1_48 = X0_48
    | k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_571,c_738,c_794,c_821])).

cnf(c_889,plain,
    ( k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48)
    | X1_48 = X0_48
    | r2_hidden(X1_48,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_888])).

cnf(c_896,plain,
    ( k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,sK4)
    | sK5 = X0_48
    | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_533,c_889])).

cnf(c_961,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_896])).

cnf(c_539,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_562,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_14,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_534,negated_conjecture,
    ( sK4 != sK5 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_543,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_754,plain,
    ( sK5 != X0_48
    | sK4 != X0_48
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_755,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_970,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_961,c_562,c_534,c_755])).

cnf(c_976,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_970])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_814,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_550,plain,
    ( ~ r2_hidden(X0_48,X0_46)
    | r2_hidden(X1_48,X1_46)
    | X1_48 != X0_48
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_756,plain,
    ( r2_hidden(X0_48,X0_46)
    | ~ r2_hidden(sK5,sK2)
    | X0_48 != sK5
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_935,plain,
    ( r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK2)
    | sK5 != sK5
    | k1_relat_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_977,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK4,sK2)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_976])).

cnf(c_1019,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_17,c_16,c_814,c_834,c_935,c_977])).

cnf(c_1023,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1019,c_779])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_317,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_318,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_455,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != X0
    | sK2 != k1_xboole_0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_318])).

cnf(c_456,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_526,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_456])).

cnf(c_1025,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1019,c_526])).

cnf(c_1037,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1025])).

cnf(c_1040,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1023,c_1037])).

cnf(c_1113,plain,
    ( r2_hidden(sK5,k1_xboole_0) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1040,c_970])).

cnf(c_532,negated_conjecture,
    ( r2_hidden(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_664,plain,
    ( r2_hidden(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_1028,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1019,c_664])).

cnf(c_541,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_816,plain,
    ( sK2 != X0_46
    | k1_xboole_0 != X0_46
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_817,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_759,plain,
    ( r2_hidden(X0_48,X0_46)
    | ~ r2_hidden(sK4,sK2)
    | X0_48 != sK4
    | X0_46 != sK2 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_760,plain,
    ( X0_48 != sK4
    | X0_46 != sK2
    | r2_hidden(X0_48,X0_46) = iProver_top
    | r2_hidden(sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_762,plain,
    ( sK4 != sK4
    | k1_xboole_0 != sK2
    | r2_hidden(sK4,sK2) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_537,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_560,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_26,plain,
    ( r2_hidden(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1113,c_1028,c_1019,c_817,c_762,c_562,c_560,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.30/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.30/1.00  
% 1.30/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.30/1.00  
% 1.30/1.00  ------  iProver source info
% 1.30/1.00  
% 1.30/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.30/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.30/1.00  git: non_committed_changes: false
% 1.30/1.00  git: last_make_outside_of_git: false
% 1.30/1.00  
% 1.30/1.00  ------ 
% 1.30/1.00  
% 1.30/1.00  ------ Input Options
% 1.30/1.00  
% 1.30/1.00  --out_options                           all
% 1.30/1.00  --tptp_safe_out                         true
% 1.30/1.00  --problem_path                          ""
% 1.30/1.00  --include_path                          ""
% 1.30/1.00  --clausifier                            res/vclausify_rel
% 1.30/1.00  --clausifier_options                    --mode clausify
% 1.30/1.00  --stdin                                 false
% 1.30/1.00  --stats_out                             all
% 1.30/1.00  
% 1.30/1.00  ------ General Options
% 1.30/1.00  
% 1.30/1.00  --fof                                   false
% 1.30/1.00  --time_out_real                         305.
% 1.30/1.00  --time_out_virtual                      -1.
% 1.30/1.00  --symbol_type_check                     false
% 1.30/1.00  --clausify_out                          false
% 1.30/1.00  --sig_cnt_out                           false
% 1.30/1.00  --trig_cnt_out                          false
% 1.30/1.00  --trig_cnt_out_tolerance                1.
% 1.30/1.00  --trig_cnt_out_sk_spl                   false
% 1.30/1.00  --abstr_cl_out                          false
% 1.30/1.00  
% 1.30/1.00  ------ Global Options
% 1.30/1.00  
% 1.30/1.00  --schedule                              default
% 1.30/1.00  --add_important_lit                     false
% 1.30/1.00  --prop_solver_per_cl                    1000
% 1.30/1.00  --min_unsat_core                        false
% 1.30/1.00  --soft_assumptions                      false
% 1.30/1.00  --soft_lemma_size                       3
% 1.30/1.00  --prop_impl_unit_size                   0
% 1.30/1.00  --prop_impl_unit                        []
% 1.30/1.00  --share_sel_clauses                     true
% 1.30/1.00  --reset_solvers                         false
% 1.30/1.00  --bc_imp_inh                            [conj_cone]
% 1.30/1.00  --conj_cone_tolerance                   3.
% 1.30/1.00  --extra_neg_conj                        none
% 1.30/1.00  --large_theory_mode                     true
% 1.30/1.00  --prolific_symb_bound                   200
% 1.30/1.00  --lt_threshold                          2000
% 1.30/1.00  --clause_weak_htbl                      true
% 1.30/1.00  --gc_record_bc_elim                     false
% 1.30/1.00  
% 1.30/1.00  ------ Preprocessing Options
% 1.30/1.00  
% 1.30/1.00  --preprocessing_flag                    true
% 1.30/1.00  --time_out_prep_mult                    0.1
% 1.30/1.00  --splitting_mode                        input
% 1.30/1.00  --splitting_grd                         true
% 1.30/1.00  --splitting_cvd                         false
% 1.30/1.00  --splitting_cvd_svl                     false
% 1.30/1.00  --splitting_nvd                         32
% 1.30/1.00  --sub_typing                            true
% 1.30/1.00  --prep_gs_sim                           true
% 1.30/1.00  --prep_unflatten                        true
% 1.30/1.00  --prep_res_sim                          true
% 1.30/1.00  --prep_upred                            true
% 1.30/1.00  --prep_sem_filter                       exhaustive
% 1.30/1.00  --prep_sem_filter_out                   false
% 1.30/1.00  --pred_elim                             true
% 1.30/1.00  --res_sim_input                         true
% 1.30/1.00  --eq_ax_congr_red                       true
% 1.30/1.00  --pure_diseq_elim                       true
% 1.30/1.00  --brand_transform                       false
% 1.30/1.00  --non_eq_to_eq                          false
% 1.30/1.00  --prep_def_merge                        true
% 1.30/1.00  --prep_def_merge_prop_impl              false
% 1.30/1.00  --prep_def_merge_mbd                    true
% 1.30/1.00  --prep_def_merge_tr_red                 false
% 1.30/1.00  --prep_def_merge_tr_cl                  false
% 1.30/1.00  --smt_preprocessing                     true
% 1.30/1.00  --smt_ac_axioms                         fast
% 1.30/1.00  --preprocessed_out                      false
% 1.30/1.00  --preprocessed_stats                    false
% 1.30/1.00  
% 1.30/1.00  ------ Abstraction refinement Options
% 1.30/1.00  
% 1.30/1.00  --abstr_ref                             []
% 1.30/1.00  --abstr_ref_prep                        false
% 1.30/1.00  --abstr_ref_until_sat                   false
% 1.30/1.00  --abstr_ref_sig_restrict                funpre
% 1.30/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.30/1.00  --abstr_ref_under                       []
% 1.30/1.00  
% 1.30/1.00  ------ SAT Options
% 1.30/1.00  
% 1.30/1.00  --sat_mode                              false
% 1.30/1.00  --sat_fm_restart_options                ""
% 1.30/1.00  --sat_gr_def                            false
% 1.30/1.00  --sat_epr_types                         true
% 1.30/1.00  --sat_non_cyclic_types                  false
% 1.30/1.00  --sat_finite_models                     false
% 1.30/1.00  --sat_fm_lemmas                         false
% 1.30/1.00  --sat_fm_prep                           false
% 1.30/1.00  --sat_fm_uc_incr                        true
% 1.30/1.00  --sat_out_model                         small
% 1.30/1.00  --sat_out_clauses                       false
% 1.30/1.00  
% 1.30/1.00  ------ QBF Options
% 1.30/1.00  
% 1.30/1.00  --qbf_mode                              false
% 1.30/1.00  --qbf_elim_univ                         false
% 1.30/1.00  --qbf_dom_inst                          none
% 1.30/1.00  --qbf_dom_pre_inst                      false
% 1.30/1.00  --qbf_sk_in                             false
% 1.30/1.00  --qbf_pred_elim                         true
% 1.30/1.00  --qbf_split                             512
% 1.30/1.00  
% 1.30/1.00  ------ BMC1 Options
% 1.30/1.00  
% 1.30/1.00  --bmc1_incremental                      false
% 1.30/1.00  --bmc1_axioms                           reachable_all
% 1.30/1.00  --bmc1_min_bound                        0
% 1.30/1.00  --bmc1_max_bound                        -1
% 1.30/1.00  --bmc1_max_bound_default                -1
% 1.30/1.00  --bmc1_symbol_reachability              true
% 1.30/1.00  --bmc1_property_lemmas                  false
% 1.30/1.00  --bmc1_k_induction                      false
% 1.30/1.00  --bmc1_non_equiv_states                 false
% 1.30/1.00  --bmc1_deadlock                         false
% 1.30/1.00  --bmc1_ucm                              false
% 1.30/1.00  --bmc1_add_unsat_core                   none
% 1.30/1.00  --bmc1_unsat_core_children              false
% 1.30/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.30/1.00  --bmc1_out_stat                         full
% 1.30/1.00  --bmc1_ground_init                      false
% 1.30/1.00  --bmc1_pre_inst_next_state              false
% 1.30/1.00  --bmc1_pre_inst_state                   false
% 1.30/1.00  --bmc1_pre_inst_reach_state             false
% 1.30/1.00  --bmc1_out_unsat_core                   false
% 1.30/1.00  --bmc1_aig_witness_out                  false
% 1.30/1.00  --bmc1_verbose                          false
% 1.30/1.00  --bmc1_dump_clauses_tptp                false
% 1.30/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.30/1.00  --bmc1_dump_file                        -
% 1.30/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.30/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.30/1.00  --bmc1_ucm_extend_mode                  1
% 1.30/1.00  --bmc1_ucm_init_mode                    2
% 1.30/1.00  --bmc1_ucm_cone_mode                    none
% 1.30/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.30/1.00  --bmc1_ucm_relax_model                  4
% 1.30/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.30/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.30/1.00  --bmc1_ucm_layered_model                none
% 1.30/1.00  --bmc1_ucm_max_lemma_size               10
% 1.30/1.00  
% 1.30/1.00  ------ AIG Options
% 1.30/1.00  
% 1.30/1.00  --aig_mode                              false
% 1.30/1.00  
% 1.30/1.00  ------ Instantiation Options
% 1.30/1.00  
% 1.30/1.00  --instantiation_flag                    true
% 1.30/1.00  --inst_sos_flag                         false
% 1.30/1.00  --inst_sos_phase                        true
% 1.30/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.30/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.30/1.00  --inst_lit_sel_side                     num_symb
% 1.30/1.00  --inst_solver_per_active                1400
% 1.30/1.00  --inst_solver_calls_frac                1.
% 1.30/1.00  --inst_passive_queue_type               priority_queues
% 1.30/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.30/1.00  --inst_passive_queues_freq              [25;2]
% 1.30/1.00  --inst_dismatching                      true
% 1.30/1.00  --inst_eager_unprocessed_to_passive     true
% 1.30/1.00  --inst_prop_sim_given                   true
% 1.30/1.00  --inst_prop_sim_new                     false
% 1.30/1.00  --inst_subs_new                         false
% 1.30/1.00  --inst_eq_res_simp                      false
% 1.30/1.00  --inst_subs_given                       false
% 1.30/1.00  --inst_orphan_elimination               true
% 1.30/1.00  --inst_learning_loop_flag               true
% 1.30/1.00  --inst_learning_start                   3000
% 1.30/1.00  --inst_learning_factor                  2
% 1.30/1.00  --inst_start_prop_sim_after_learn       3
% 1.30/1.00  --inst_sel_renew                        solver
% 1.30/1.00  --inst_lit_activity_flag                true
% 1.30/1.00  --inst_restr_to_given                   false
% 1.30/1.00  --inst_activity_threshold               500
% 1.30/1.00  --inst_out_proof                        true
% 1.30/1.00  
% 1.30/1.00  ------ Resolution Options
% 1.30/1.00  
% 1.30/1.00  --resolution_flag                       true
% 1.30/1.00  --res_lit_sel                           adaptive
% 1.30/1.00  --res_lit_sel_side                      none
% 1.30/1.00  --res_ordering                          kbo
% 1.30/1.00  --res_to_prop_solver                    active
% 1.30/1.00  --res_prop_simpl_new                    false
% 1.30/1.00  --res_prop_simpl_given                  true
% 1.30/1.00  --res_passive_queue_type                priority_queues
% 1.30/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.30/1.00  --res_passive_queues_freq               [15;5]
% 1.30/1.00  --res_forward_subs                      full
% 1.30/1.00  --res_backward_subs                     full
% 1.30/1.00  --res_forward_subs_resolution           true
% 1.30/1.00  --res_backward_subs_resolution          true
% 1.30/1.00  --res_orphan_elimination                true
% 1.30/1.00  --res_time_limit                        2.
% 1.30/1.00  --res_out_proof                         true
% 1.30/1.00  
% 1.30/1.00  ------ Superposition Options
% 1.30/1.00  
% 1.30/1.00  --superposition_flag                    true
% 1.30/1.00  --sup_passive_queue_type                priority_queues
% 1.30/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.30/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.30/1.00  --demod_completeness_check              fast
% 1.30/1.00  --demod_use_ground                      true
% 1.30/1.00  --sup_to_prop_solver                    passive
% 1.30/1.00  --sup_prop_simpl_new                    true
% 1.30/1.00  --sup_prop_simpl_given                  true
% 1.30/1.00  --sup_fun_splitting                     false
% 1.30/1.00  --sup_smt_interval                      50000
% 1.30/1.00  
% 1.30/1.00  ------ Superposition Simplification Setup
% 1.30/1.00  
% 1.30/1.00  --sup_indices_passive                   []
% 1.30/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.30/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.00  --sup_full_bw                           [BwDemod]
% 1.30/1.00  --sup_immed_triv                        [TrivRules]
% 1.30/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.30/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.00  --sup_immed_bw_main                     []
% 1.30/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.30/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.00  
% 1.30/1.00  ------ Combination Options
% 1.30/1.00  
% 1.30/1.00  --comb_res_mult                         3
% 1.30/1.00  --comb_sup_mult                         2
% 1.30/1.00  --comb_inst_mult                        10
% 1.30/1.00  
% 1.30/1.00  ------ Debug Options
% 1.30/1.00  
% 1.30/1.00  --dbg_backtrace                         false
% 1.30/1.00  --dbg_dump_prop_clauses                 false
% 1.30/1.00  --dbg_dump_prop_clauses_file            -
% 1.30/1.00  --dbg_out_stat                          false
% 1.30/1.00  ------ Parsing...
% 1.30/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.30/1.00  
% 1.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.30/1.00  
% 1.30/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.30/1.00  
% 1.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.30/1.00  ------ Proving...
% 1.30/1.00  ------ Problem Properties 
% 1.30/1.00  
% 1.30/1.00  
% 1.30/1.00  clauses                                 11
% 1.30/1.00  conjectures                             4
% 1.30/1.00  EPR                                     3
% 1.30/1.00  Horn                                    9
% 1.30/1.00  unary                                   5
% 1.30/1.00  binary                                  2
% 1.30/1.00  lits                                    24
% 1.30/1.00  lits eq                                 16
% 1.30/1.00  fd_pure                                 0
% 1.30/1.00  fd_pseudo                               0
% 1.30/1.00  fd_cond                                 0
% 1.30/1.00  fd_pseudo_cond                          1
% 1.30/1.00  AC symbols                              0
% 1.30/1.00  
% 1.30/1.00  ------ Schedule dynamic 5 is on 
% 1.30/1.00  
% 1.30/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.30/1.00  
% 1.30/1.00  
% 1.30/1.00  ------ 
% 1.30/1.00  Current options:
% 1.30/1.00  ------ 
% 1.30/1.00  
% 1.30/1.00  ------ Input Options
% 1.30/1.00  
% 1.30/1.00  --out_options                           all
% 1.30/1.00  --tptp_safe_out                         true
% 1.30/1.00  --problem_path                          ""
% 1.30/1.00  --include_path                          ""
% 1.30/1.00  --clausifier                            res/vclausify_rel
% 1.30/1.00  --clausifier_options                    --mode clausify
% 1.30/1.00  --stdin                                 false
% 1.30/1.00  --stats_out                             all
% 1.30/1.00  
% 1.30/1.00  ------ General Options
% 1.30/1.00  
% 1.30/1.00  --fof                                   false
% 1.30/1.00  --time_out_real                         305.
% 1.30/1.00  --time_out_virtual                      -1.
% 1.30/1.00  --symbol_type_check                     false
% 1.30/1.00  --clausify_out                          false
% 1.30/1.00  --sig_cnt_out                           false
% 1.30/1.00  --trig_cnt_out                          false
% 1.30/1.00  --trig_cnt_out_tolerance                1.
% 1.30/1.00  --trig_cnt_out_sk_spl                   false
% 1.30/1.00  --abstr_cl_out                          false
% 1.30/1.00  
% 1.30/1.00  ------ Global Options
% 1.30/1.00  
% 1.30/1.00  --schedule                              default
% 1.30/1.00  --add_important_lit                     false
% 1.30/1.00  --prop_solver_per_cl                    1000
% 1.30/1.00  --min_unsat_core                        false
% 1.30/1.00  --soft_assumptions                      false
% 1.30/1.00  --soft_lemma_size                       3
% 1.30/1.00  --prop_impl_unit_size                   0
% 1.30/1.00  --prop_impl_unit                        []
% 1.30/1.00  --share_sel_clauses                     true
% 1.30/1.00  --reset_solvers                         false
% 1.30/1.00  --bc_imp_inh                            [conj_cone]
% 1.30/1.00  --conj_cone_tolerance                   3.
% 1.30/1.00  --extra_neg_conj                        none
% 1.30/1.00  --large_theory_mode                     true
% 1.30/1.00  --prolific_symb_bound                   200
% 1.30/1.00  --lt_threshold                          2000
% 1.30/1.00  --clause_weak_htbl                      true
% 1.30/1.00  --gc_record_bc_elim                     false
% 1.30/1.00  
% 1.30/1.00  ------ Preprocessing Options
% 1.30/1.00  
% 1.30/1.00  --preprocessing_flag                    true
% 1.30/1.00  --time_out_prep_mult                    0.1
% 1.30/1.00  --splitting_mode                        input
% 1.30/1.00  --splitting_grd                         true
% 1.30/1.00  --splitting_cvd                         false
% 1.30/1.00  --splitting_cvd_svl                     false
% 1.30/1.00  --splitting_nvd                         32
% 1.30/1.00  --sub_typing                            true
% 1.30/1.00  --prep_gs_sim                           true
% 1.30/1.00  --prep_unflatten                        true
% 1.30/1.00  --prep_res_sim                          true
% 1.30/1.00  --prep_upred                            true
% 1.30/1.00  --prep_sem_filter                       exhaustive
% 1.30/1.00  --prep_sem_filter_out                   false
% 1.30/1.00  --pred_elim                             true
% 1.30/1.00  --res_sim_input                         true
% 1.30/1.00  --eq_ax_congr_red                       true
% 1.30/1.00  --pure_diseq_elim                       true
% 1.30/1.00  --brand_transform                       false
% 1.30/1.00  --non_eq_to_eq                          false
% 1.30/1.00  --prep_def_merge                        true
% 1.30/1.00  --prep_def_merge_prop_impl              false
% 1.30/1.00  --prep_def_merge_mbd                    true
% 1.30/1.00  --prep_def_merge_tr_red                 false
% 1.30/1.00  --prep_def_merge_tr_cl                  false
% 1.30/1.00  --smt_preprocessing                     true
% 1.30/1.00  --smt_ac_axioms                         fast
% 1.30/1.00  --preprocessed_out                      false
% 1.30/1.00  --preprocessed_stats                    false
% 1.30/1.00  
% 1.30/1.00  ------ Abstraction refinement Options
% 1.30/1.00  
% 1.30/1.00  --abstr_ref                             []
% 1.30/1.00  --abstr_ref_prep                        false
% 1.30/1.00  --abstr_ref_until_sat                   false
% 1.30/1.00  --abstr_ref_sig_restrict                funpre
% 1.30/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.30/1.00  --abstr_ref_under                       []
% 1.30/1.00  
% 1.30/1.00  ------ SAT Options
% 1.30/1.00  
% 1.30/1.00  --sat_mode                              false
% 1.30/1.00  --sat_fm_restart_options                ""
% 1.30/1.00  --sat_gr_def                            false
% 1.30/1.00  --sat_epr_types                         true
% 1.30/1.00  --sat_non_cyclic_types                  false
% 1.30/1.00  --sat_finite_models                     false
% 1.30/1.00  --sat_fm_lemmas                         false
% 1.30/1.00  --sat_fm_prep                           false
% 1.30/1.00  --sat_fm_uc_incr                        true
% 1.30/1.00  --sat_out_model                         small
% 1.30/1.00  --sat_out_clauses                       false
% 1.30/1.00  
% 1.30/1.00  ------ QBF Options
% 1.30/1.00  
% 1.30/1.00  --qbf_mode                              false
% 1.30/1.00  --qbf_elim_univ                         false
% 1.30/1.00  --qbf_dom_inst                          none
% 1.30/1.00  --qbf_dom_pre_inst                      false
% 1.30/1.00  --qbf_sk_in                             false
% 1.30/1.00  --qbf_pred_elim                         true
% 1.30/1.00  --qbf_split                             512
% 1.30/1.00  
% 1.30/1.00  ------ BMC1 Options
% 1.30/1.00  
% 1.30/1.00  --bmc1_incremental                      false
% 1.30/1.00  --bmc1_axioms                           reachable_all
% 1.30/1.00  --bmc1_min_bound                        0
% 1.30/1.00  --bmc1_max_bound                        -1
% 1.30/1.00  --bmc1_max_bound_default                -1
% 1.30/1.00  --bmc1_symbol_reachability              true
% 1.30/1.00  --bmc1_property_lemmas                  false
% 1.30/1.00  --bmc1_k_induction                      false
% 1.30/1.00  --bmc1_non_equiv_states                 false
% 1.30/1.00  --bmc1_deadlock                         false
% 1.30/1.00  --bmc1_ucm                              false
% 1.30/1.00  --bmc1_add_unsat_core                   none
% 1.30/1.00  --bmc1_unsat_core_children              false
% 1.30/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.30/1.00  --bmc1_out_stat                         full
% 1.30/1.00  --bmc1_ground_init                      false
% 1.30/1.00  --bmc1_pre_inst_next_state              false
% 1.30/1.00  --bmc1_pre_inst_state                   false
% 1.30/1.00  --bmc1_pre_inst_reach_state             false
% 1.30/1.00  --bmc1_out_unsat_core                   false
% 1.30/1.00  --bmc1_aig_witness_out                  false
% 1.30/1.00  --bmc1_verbose                          false
% 1.30/1.00  --bmc1_dump_clauses_tptp                false
% 1.30/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.30/1.00  --bmc1_dump_file                        -
% 1.30/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.30/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.30/1.00  --bmc1_ucm_extend_mode                  1
% 1.30/1.00  --bmc1_ucm_init_mode                    2
% 1.30/1.00  --bmc1_ucm_cone_mode                    none
% 1.30/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.30/1.00  --bmc1_ucm_relax_model                  4
% 1.30/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.30/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.30/1.00  --bmc1_ucm_layered_model                none
% 1.30/1.00  --bmc1_ucm_max_lemma_size               10
% 1.30/1.00  
% 1.30/1.00  ------ AIG Options
% 1.30/1.00  
% 1.30/1.00  --aig_mode                              false
% 1.30/1.00  
% 1.30/1.00  ------ Instantiation Options
% 1.30/1.00  
% 1.30/1.00  --instantiation_flag                    true
% 1.30/1.00  --inst_sos_flag                         false
% 1.30/1.00  --inst_sos_phase                        true
% 1.30/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.30/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.30/1.00  --inst_lit_sel_side                     none
% 1.30/1.00  --inst_solver_per_active                1400
% 1.30/1.00  --inst_solver_calls_frac                1.
% 1.30/1.00  --inst_passive_queue_type               priority_queues
% 1.30/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.30/1.00  --inst_passive_queues_freq              [25;2]
% 1.30/1.00  --inst_dismatching                      true
% 1.30/1.00  --inst_eager_unprocessed_to_passive     true
% 1.30/1.00  --inst_prop_sim_given                   true
% 1.30/1.00  --inst_prop_sim_new                     false
% 1.30/1.00  --inst_subs_new                         false
% 1.30/1.00  --inst_eq_res_simp                      false
% 1.30/1.00  --inst_subs_given                       false
% 1.30/1.00  --inst_orphan_elimination               true
% 1.30/1.00  --inst_learning_loop_flag               true
% 1.30/1.00  --inst_learning_start                   3000
% 1.30/1.00  --inst_learning_factor                  2
% 1.30/1.00  --inst_start_prop_sim_after_learn       3
% 1.30/1.00  --inst_sel_renew                        solver
% 1.30/1.00  --inst_lit_activity_flag                true
% 1.30/1.00  --inst_restr_to_given                   false
% 1.30/1.00  --inst_activity_threshold               500
% 1.30/1.00  --inst_out_proof                        true
% 1.30/1.00  
% 1.30/1.00  ------ Resolution Options
% 1.30/1.00  
% 1.30/1.00  --resolution_flag                       false
% 1.30/1.00  --res_lit_sel                           adaptive
% 1.30/1.00  --res_lit_sel_side                      none
% 1.30/1.01  --res_ordering                          kbo
% 1.30/1.01  --res_to_prop_solver                    active
% 1.30/1.01  --res_prop_simpl_new                    false
% 1.30/1.01  --res_prop_simpl_given                  true
% 1.30/1.01  --res_passive_queue_type                priority_queues
% 1.30/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.30/1.01  --res_passive_queues_freq               [15;5]
% 1.30/1.01  --res_forward_subs                      full
% 1.30/1.01  --res_backward_subs                     full
% 1.30/1.01  --res_forward_subs_resolution           true
% 1.30/1.01  --res_backward_subs_resolution          true
% 1.30/1.01  --res_orphan_elimination                true
% 1.30/1.01  --res_time_limit                        2.
% 1.30/1.01  --res_out_proof                         true
% 1.30/1.01  
% 1.30/1.01  ------ Superposition Options
% 1.30/1.01  
% 1.30/1.01  --superposition_flag                    true
% 1.30/1.01  --sup_passive_queue_type                priority_queues
% 1.30/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.30/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.30/1.01  --demod_completeness_check              fast
% 1.30/1.01  --demod_use_ground                      true
% 1.30/1.01  --sup_to_prop_solver                    passive
% 1.30/1.01  --sup_prop_simpl_new                    true
% 1.30/1.01  --sup_prop_simpl_given                  true
% 1.30/1.01  --sup_fun_splitting                     false
% 1.30/1.01  --sup_smt_interval                      50000
% 1.30/1.01  
% 1.30/1.01  ------ Superposition Simplification Setup
% 1.30/1.01  
% 1.30/1.01  --sup_indices_passive                   []
% 1.30/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.30/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.30/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_full_bw                           [BwDemod]
% 1.30/1.01  --sup_immed_triv                        [TrivRules]
% 1.30/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.30/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_immed_bw_main                     []
% 1.30/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.30/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.30/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.30/1.01  
% 1.30/1.01  ------ Combination Options
% 1.30/1.01  
% 1.30/1.01  --comb_res_mult                         3
% 1.30/1.01  --comb_sup_mult                         2
% 1.30/1.01  --comb_inst_mult                        10
% 1.30/1.01  
% 1.30/1.01  ------ Debug Options
% 1.30/1.01  
% 1.30/1.01  --dbg_backtrace                         false
% 1.30/1.01  --dbg_dump_prop_clauses                 false
% 1.30/1.01  --dbg_dump_prop_clauses_file            -
% 1.30/1.01  --dbg_out_stat                          false
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  ------ Proving...
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  % SZS status Theorem for theBenchmark.p
% 1.30/1.01  
% 1.30/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.30/1.01  
% 1.30/1.01  fof(f6,conjecture,(
% 1.30/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f7,negated_conjecture,(
% 1.30/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.30/1.01    inference(negated_conjecture,[],[f6])).
% 1.30/1.01  
% 1.30/1.01  fof(f14,plain,(
% 1.30/1.01    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.30/1.01    inference(ennf_transformation,[],[f7])).
% 1.30/1.01  
% 1.30/1.01  fof(f15,plain,(
% 1.30/1.01    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.30/1.01    inference(flattening,[],[f14])).
% 1.30/1.01  
% 1.30/1.01  fof(f22,plain,(
% 1.30/1.01    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f21,plain,(
% 1.30/1.01    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f23,plain,(
% 1.30/1.01    (sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 1.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f15,f22,f21])).
% 1.30/1.01  
% 1.30/1.01  fof(f39,plain,(
% 1.30/1.01    v1_funct_2(sK3,sK2,sK2)),
% 1.30/1.01    inference(cnf_transformation,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f5,axiom,(
% 1.30/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f12,plain,(
% 1.30/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/1.01    inference(ennf_transformation,[],[f5])).
% 1.30/1.01  
% 1.30/1.01  fof(f13,plain,(
% 1.30/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/1.01    inference(flattening,[],[f12])).
% 1.30/1.01  
% 1.30/1.01  fof(f20,plain,(
% 1.30/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/1.01    inference(nnf_transformation,[],[f13])).
% 1.30/1.01  
% 1.30/1.01  fof(f32,plain,(
% 1.30/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/1.01    inference(cnf_transformation,[],[f20])).
% 1.30/1.01  
% 1.30/1.01  fof(f40,plain,(
% 1.30/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 1.30/1.01    inference(cnf_transformation,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f4,axiom,(
% 1.30/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f11,plain,(
% 1.30/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/1.01    inference(ennf_transformation,[],[f4])).
% 1.30/1.01  
% 1.30/1.01  fof(f31,plain,(
% 1.30/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/1.01    inference(cnf_transformation,[],[f11])).
% 1.30/1.01  
% 1.30/1.01  fof(f44,plain,(
% 1.30/1.01    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 1.30/1.01    inference(cnf_transformation,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f3,axiom,(
% 1.30/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f9,plain,(
% 1.30/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.30/1.01    inference(ennf_transformation,[],[f3])).
% 1.30/1.01  
% 1.30/1.01  fof(f10,plain,(
% 1.30/1.01    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/1.01    inference(flattening,[],[f9])).
% 1.30/1.01  
% 1.30/1.01  fof(f16,plain,(
% 1.30/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/1.01    inference(nnf_transformation,[],[f10])).
% 1.30/1.01  
% 1.30/1.01  fof(f17,plain,(
% 1.30/1.01    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/1.01    inference(rectify,[],[f16])).
% 1.30/1.01  
% 1.30/1.01  fof(f18,plain,(
% 1.30/1.01    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 1.30/1.01    introduced(choice_axiom,[])).
% 1.30/1.01  
% 1.30/1.01  fof(f19,plain,(
% 1.30/1.01    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 1.30/1.01  
% 1.30/1.01  fof(f26,plain,(
% 1.30/1.01    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f19])).
% 1.30/1.01  
% 1.30/1.01  fof(f38,plain,(
% 1.30/1.01    v1_funct_1(sK3)),
% 1.30/1.01    inference(cnf_transformation,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f41,plain,(
% 1.30/1.01    v2_funct_1(sK3)),
% 1.30/1.01    inference(cnf_transformation,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f1,axiom,(
% 1.30/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f8,plain,(
% 1.30/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.30/1.01    inference(ennf_transformation,[],[f1])).
% 1.30/1.01  
% 1.30/1.01  fof(f24,plain,(
% 1.30/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.30/1.01    inference(cnf_transformation,[],[f8])).
% 1.30/1.01  
% 1.30/1.01  fof(f2,axiom,(
% 1.30/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.30/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.30/1.01  
% 1.30/1.01  fof(f25,plain,(
% 1.30/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.30/1.01    inference(cnf_transformation,[],[f2])).
% 1.30/1.01  
% 1.30/1.01  fof(f45,plain,(
% 1.30/1.01    sK4 != sK5),
% 1.30/1.01    inference(cnf_transformation,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f42,plain,(
% 1.30/1.01    r2_hidden(sK4,sK2)),
% 1.30/1.01    inference(cnf_transformation,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f43,plain,(
% 1.30/1.01    r2_hidden(sK5,sK2)),
% 1.30/1.01    inference(cnf_transformation,[],[f23])).
% 1.30/1.01  
% 1.30/1.01  fof(f33,plain,(
% 1.30/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.30/1.01    inference(cnf_transformation,[],[f20])).
% 1.30/1.01  
% 1.30/1.01  fof(f50,plain,(
% 1.30/1.01    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.30/1.01    inference(equality_resolution,[],[f33])).
% 1.30/1.01  
% 1.30/1.01  cnf(c_20,negated_conjecture,
% 1.30/1.01      ( v1_funct_2(sK3,sK2,sK2) ),
% 1.30/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_13,plain,
% 1.30/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.30/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.30/1.01      | k1_relset_1(X1,X2,X0) = X1
% 1.30/1.01      | k1_xboole_0 = X2 ),
% 1.30/1.01      inference(cnf_transformation,[],[f32]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_19,negated_conjecture,
% 1.30/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 1.30/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_237,plain,
% 1.30/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.30/1.01      | k1_relset_1(X1,X2,X0) = X1
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | sK3 != X0
% 1.30/1.01      | k1_xboole_0 = X2 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_238,plain,
% 1.30/1.01      ( ~ v1_funct_2(sK3,X0,X1)
% 1.30/1.01      | k1_relset_1(X0,X1,sK3) = X0
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | k1_xboole_0 = X1 ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_237]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_430,plain,
% 1.30/1.01      ( k1_relset_1(X0,X1,sK3) = X0
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | sK2 != X0
% 1.30/1.01      | sK2 != X1
% 1.30/1.01      | sK3 != sK3
% 1.30/1.01      | k1_xboole_0 = X1 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_238]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_431,plain,
% 1.30/1.01      ( k1_relset_1(sK2,sK2,sK3) = sK2
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | k1_xboole_0 = sK2 ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_430]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_489,plain,
% 1.30/1.01      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 1.30/1.01      inference(equality_resolution_simp,[status(thm)],[c_431]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_525,plain,
% 1.30/1.01      ( k1_relset_1(sK2,sK2,sK3) = sK2 | k1_xboole_0 = sK2 ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_489]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_7,plain,
% 1.30/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.30/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.30/1.01      inference(cnf_transformation,[],[f31]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_273,plain,
% 1.30/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | sK3 != X2 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_274,plain,
% 1.30/1.01      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_273]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_529,plain,
% 1.30/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | k1_relset_1(X0_46,X1_46,sK3) = k1_relat_1(sK3) ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_274]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_779,plain,
% 1.30/1.01      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 1.30/1.01      inference(equality_resolution,[status(thm)],[c_529]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_834,plain,
% 1.30/1.01      ( k1_relat_1(sK3) = sK2 | sK2 = k1_xboole_0 ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_525,c_779]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_15,negated_conjecture,
% 1.30/1.01      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.30/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_533,negated_conjecture,
% 1.30/1.01      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_6,plain,
% 1.30/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.30/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.30/1.01      | ~ v1_funct_1(X1)
% 1.30/1.01      | ~ v2_funct_1(X1)
% 1.30/1.01      | ~ v1_relat_1(X1)
% 1.30/1.01      | X0 = X2
% 1.30/1.01      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 1.30/1.01      inference(cnf_transformation,[],[f26]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_21,negated_conjecture,
% 1.30/1.01      ( v1_funct_1(sK3) ),
% 1.30/1.01      inference(cnf_transformation,[],[f38]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_381,plain,
% 1.30/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 1.30/1.01      | ~ r2_hidden(X2,k1_relat_1(X1))
% 1.30/1.01      | ~ v2_funct_1(X1)
% 1.30/1.01      | ~ v1_relat_1(X1)
% 1.30/1.01      | X0 = X2
% 1.30/1.01      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 1.30/1.01      | sK3 != X1 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_382,plain,
% 1.30/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.30/1.01      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.30/1.01      | ~ v2_funct_1(sK3)
% 1.30/1.01      | ~ v1_relat_1(sK3)
% 1.30/1.01      | X1 = X0
% 1.30/1.01      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_381]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_18,negated_conjecture,
% 1.30/1.01      ( v2_funct_1(sK3) ),
% 1.30/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_386,plain,
% 1.30/1.01      ( ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.30/1.01      | ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.30/1.01      | ~ v1_relat_1(sK3)
% 1.30/1.01      | X1 = X0
% 1.30/1.01      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_382,c_18]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_387,plain,
% 1.30/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.30/1.01      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 1.30/1.01      | ~ v1_relat_1(sK3)
% 1.30/1.01      | X1 = X0
% 1.30/1.01      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) ),
% 1.30/1.01      inference(renaming,[status(thm)],[c_386]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_528,plain,
% 1.30/1.01      ( ~ r2_hidden(X0_48,k1_relat_1(sK3))
% 1.30/1.01      | ~ r2_hidden(X1_48,k1_relat_1(sK3))
% 1.30/1.01      | ~ v1_relat_1(sK3)
% 1.30/1.01      | k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48)
% 1.30/1.01      | X1_48 = X0_48 ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_387]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_667,plain,
% 1.30/1.01      ( k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48)
% 1.30/1.01      | X1_48 = X0_48
% 1.30/1.01      | r2_hidden(X1_48,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | v1_relat_1(sK3) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_571,plain,
% 1.30/1.01      ( k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48)
% 1.30/1.01      | X1_48 = X0_48
% 1.30/1.01      | r2_hidden(X1_48,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | v1_relat_1(sK3) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_538,plain,( X0_47 = X0_47 ),theory(equality) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_738,plain,
% 1.30/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_538]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_0,plain,
% 1.30/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.30/1.01      | ~ v1_relat_1(X1)
% 1.30/1.01      | v1_relat_1(X0) ),
% 1.30/1.01      inference(cnf_transformation,[],[f24]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_222,plain,
% 1.30/1.01      ( ~ v1_relat_1(X0)
% 1.30/1.01      | v1_relat_1(X1)
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0)
% 1.30/1.01      | sK3 != X1 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_223,plain,
% 1.30/1.01      ( ~ v1_relat_1(X0)
% 1.30/1.01      | v1_relat_1(sK3)
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_222]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_530,plain,
% 1.30/1.01      ( ~ v1_relat_1(X0_46)
% 1.30/1.01      | v1_relat_1(sK3)
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(X0_46) ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_223]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_733,plain,
% 1.30/1.01      ( ~ v1_relat_1(k2_zfmisc_1(X0_46,X1_46))
% 1.30/1.01      | v1_relat_1(sK3)
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_530]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_793,plain,
% 1.30/1.01      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | v1_relat_1(sK3)
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_733]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_794,plain,
% 1.30/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | v1_relat_1(k2_zfmisc_1(sK2,sK2)) != iProver_top
% 1.30/1.01      | v1_relat_1(sK3) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1,plain,
% 1.30/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.30/1.01      inference(cnf_transformation,[],[f25]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_535,plain,
% 1.30/1.01      ( v1_relat_1(k2_zfmisc_1(X0_46,X1_46)) ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_820,plain,
% 1.30/1.01      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_535]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_821,plain,
% 1.30/1.01      ( v1_relat_1(k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_888,plain,
% 1.30/1.01      ( r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | r2_hidden(X1_48,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | X1_48 = X0_48
% 1.30/1.01      | k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48) ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_667,c_571,c_738,c_794,c_821]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_889,plain,
% 1.30/1.01      ( k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,X1_48)
% 1.30/1.01      | X1_48 = X0_48
% 1.30/1.01      | r2_hidden(X1_48,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top ),
% 1.30/1.01      inference(renaming,[status(thm)],[c_888]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_896,plain,
% 1.30/1.01      ( k1_funct_1(sK3,X0_48) != k1_funct_1(sK3,sK4)
% 1.30/1.01      | sK5 = X0_48
% 1.30/1.01      | r2_hidden(X0_48,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_533,c_889]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_961,plain,
% 1.30/1.01      ( sK5 = sK4
% 1.30/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 1.30/1.01      inference(equality_resolution,[status(thm)],[c_896]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_539,plain,( X0_48 = X0_48 ),theory(equality) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_562,plain,
% 1.30/1.01      ( sK4 = sK4 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_539]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_14,negated_conjecture,
% 1.30/1.01      ( sK4 != sK5 ),
% 1.30/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_534,negated_conjecture,
% 1.30/1.01      ( sK4 != sK5 ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_543,plain,
% 1.30/1.01      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 1.30/1.01      theory(equality) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_754,plain,
% 1.30/1.01      ( sK5 != X0_48 | sK4 != X0_48 | sK4 = sK5 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_543]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_755,plain,
% 1.30/1.01      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_754]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_970,plain,
% 1.30/1.01      ( r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | r2_hidden(sK4,k1_relat_1(sK3)) != iProver_top ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_961,c_562,c_534,c_755]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_976,plain,
% 1.30/1.01      ( sK2 = k1_xboole_0
% 1.30/1.01      | r2_hidden(sK5,k1_relat_1(sK3)) != iProver_top
% 1.30/1.01      | r2_hidden(sK4,sK2) != iProver_top ),
% 1.30/1.01      inference(superposition,[status(thm)],[c_834,c_970]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_17,negated_conjecture,
% 1.30/1.01      ( r2_hidden(sK4,sK2) ),
% 1.30/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_16,negated_conjecture,
% 1.30/1.01      ( r2_hidden(sK5,sK2) ),
% 1.30/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_814,plain,
% 1.30/1.01      ( sK5 = sK5 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_539]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_550,plain,
% 1.30/1.01      ( ~ r2_hidden(X0_48,X0_46)
% 1.30/1.01      | r2_hidden(X1_48,X1_46)
% 1.30/1.01      | X1_48 != X0_48
% 1.30/1.01      | X1_46 != X0_46 ),
% 1.30/1.01      theory(equality) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_756,plain,
% 1.30/1.01      ( r2_hidden(X0_48,X0_46)
% 1.30/1.01      | ~ r2_hidden(sK5,sK2)
% 1.30/1.01      | X0_48 != sK5
% 1.30/1.01      | X0_46 != sK2 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_550]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_935,plain,
% 1.30/1.01      ( r2_hidden(sK5,k1_relat_1(sK3))
% 1.30/1.01      | ~ r2_hidden(sK5,sK2)
% 1.30/1.01      | sK5 != sK5
% 1.30/1.01      | k1_relat_1(sK3) != sK2 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_756]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_977,plain,
% 1.30/1.01      ( ~ r2_hidden(sK5,k1_relat_1(sK3))
% 1.30/1.01      | ~ r2_hidden(sK4,sK2)
% 1.30/1.01      | sK2 = k1_xboole_0 ),
% 1.30/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_976]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1019,plain,
% 1.30/1.01      ( sK2 = k1_xboole_0 ),
% 1.30/1.01      inference(global_propositional_subsumption,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_976,c_17,c_16,c_814,c_834,c_935,c_977]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1023,plain,
% 1.30/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_1019,c_779]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_12,plain,
% 1.30/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.30/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.30/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 1.30/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_317,plain,
% 1.30/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.30/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | sK3 != X0 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_318,plain,
% 1.30/1.01      ( ~ v1_funct_2(sK3,k1_xboole_0,X0)
% 1.30/1.01      | k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)) ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_317]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_455,plain,
% 1.30/1.01      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | sK2 != X0
% 1.30/1.01      | sK2 != k1_xboole_0
% 1.30/1.01      | sK3 != sK3 ),
% 1.30/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_318]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_456,plain,
% 1.30/1.01      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.30/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | sK2 != k1_xboole_0 ),
% 1.30/1.01      inference(unflattening,[status(thm)],[c_455]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_526,plain,
% 1.30/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))
% 1.30/1.01      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 1.30/1.01      | sK2 != k1_xboole_0 ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_456]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1025,plain,
% 1.30/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.30/1.01      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 1.30/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_1019,c_526]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1037,plain,
% 1.30/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 1.30/1.01      inference(equality_resolution_simp,[status(thm)],[c_1025]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1040,plain,
% 1.30/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.30/1.01      inference(light_normalisation,[status(thm)],[c_1023,c_1037]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1113,plain,
% 1.30/1.01      ( r2_hidden(sK5,k1_xboole_0) != iProver_top
% 1.30/1.01      | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_1040,c_970]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_532,negated_conjecture,
% 1.30/1.01      ( r2_hidden(sK5,sK2) ),
% 1.30/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_664,plain,
% 1.30/1.01      ( r2_hidden(sK5,sK2) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_1028,plain,
% 1.30/1.01      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 1.30/1.01      inference(demodulation,[status(thm)],[c_1019,c_664]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_541,plain,
% 1.30/1.01      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 1.30/1.01      theory(equality) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_816,plain,
% 1.30/1.01      ( sK2 != X0_46 | k1_xboole_0 != X0_46 | k1_xboole_0 = sK2 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_541]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_817,plain,
% 1.30/1.01      ( sK2 != k1_xboole_0
% 1.30/1.01      | k1_xboole_0 = sK2
% 1.30/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_816]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_759,plain,
% 1.30/1.01      ( r2_hidden(X0_48,X0_46)
% 1.30/1.01      | ~ r2_hidden(sK4,sK2)
% 1.30/1.01      | X0_48 != sK4
% 1.30/1.01      | X0_46 != sK2 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_550]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_760,plain,
% 1.30/1.01      ( X0_48 != sK4
% 1.30/1.01      | X0_46 != sK2
% 1.30/1.01      | r2_hidden(X0_48,X0_46) = iProver_top
% 1.30/1.01      | r2_hidden(sK4,sK2) != iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_762,plain,
% 1.30/1.01      ( sK4 != sK4
% 1.30/1.01      | k1_xboole_0 != sK2
% 1.30/1.01      | r2_hidden(sK4,sK2) != iProver_top
% 1.30/1.01      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_760]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_537,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_560,plain,
% 1.30/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 1.30/1.01      inference(instantiation,[status(thm)],[c_537]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(c_26,plain,
% 1.30/1.01      ( r2_hidden(sK4,sK2) = iProver_top ),
% 1.30/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.30/1.01  
% 1.30/1.01  cnf(contradiction,plain,
% 1.30/1.01      ( $false ),
% 1.30/1.01      inference(minisat,
% 1.30/1.01                [status(thm)],
% 1.30/1.01                [c_1113,c_1028,c_1019,c_817,c_762,c_562,c_560,c_26]) ).
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.30/1.01  
% 1.30/1.01  ------                               Statistics
% 1.30/1.01  
% 1.30/1.01  ------ General
% 1.30/1.01  
% 1.30/1.01  abstr_ref_over_cycles:                  0
% 1.30/1.01  abstr_ref_under_cycles:                 0
% 1.30/1.01  gc_basic_clause_elim:                   0
% 1.30/1.01  forced_gc_time:                         0
% 1.30/1.01  parsing_time:                           0.01
% 1.30/1.01  unif_index_cands_time:                  0.
% 1.30/1.01  unif_index_add_time:                    0.
% 1.30/1.01  orderings_time:                         0.
% 1.30/1.01  out_proof_time:                         0.012
% 1.30/1.01  total_time:                             0.082
% 1.30/1.01  num_of_symbols:                         53
% 1.30/1.01  num_of_terms:                           1146
% 1.30/1.01  
% 1.30/1.01  ------ Preprocessing
% 1.30/1.01  
% 1.30/1.01  num_of_splits:                          0
% 1.30/1.01  num_of_split_atoms:                     0
% 1.30/1.01  num_of_reused_defs:                     0
% 1.30/1.01  num_eq_ax_congr_red:                    5
% 1.30/1.01  num_of_sem_filtered_clauses:            1
% 1.30/1.01  num_of_subtypes:                        4
% 1.30/1.01  monotx_restored_types:                  0
% 1.30/1.01  sat_num_of_epr_types:                   0
% 1.30/1.01  sat_num_of_non_cyclic_types:            0
% 1.30/1.01  sat_guarded_non_collapsed_types:        1
% 1.30/1.01  num_pure_diseq_elim:                    0
% 1.30/1.01  simp_replaced_by:                       0
% 1.30/1.01  res_preprocessed:                       86
% 1.30/1.01  prep_upred:                             0
% 1.30/1.01  prep_unflattend:                        29
% 1.30/1.01  smt_new_axioms:                         0
% 1.30/1.01  pred_elim_cands:                        2
% 1.30/1.01  pred_elim:                              4
% 1.30/1.01  pred_elim_cl:                           11
% 1.30/1.01  pred_elim_cycles:                       6
% 1.30/1.01  merged_defs:                            0
% 1.30/1.01  merged_defs_ncl:                        0
% 1.30/1.01  bin_hyper_res:                          0
% 1.30/1.01  prep_cycles:                            4
% 1.30/1.01  pred_elim_time:                         0.005
% 1.30/1.01  splitting_time:                         0.
% 1.30/1.01  sem_filter_time:                        0.
% 1.30/1.01  monotx_time:                            0.
% 1.30/1.01  subtype_inf_time:                       0.
% 1.30/1.01  
% 1.30/1.01  ------ Problem properties
% 1.30/1.01  
% 1.30/1.01  clauses:                                11
% 1.30/1.01  conjectures:                            4
% 1.30/1.01  epr:                                    3
% 1.30/1.01  horn:                                   9
% 1.30/1.01  ground:                                 7
% 1.30/1.01  unary:                                  5
% 1.30/1.01  binary:                                 2
% 1.30/1.01  lits:                                   24
% 1.30/1.01  lits_eq:                                16
% 1.30/1.01  fd_pure:                                0
% 1.30/1.01  fd_pseudo:                              0
% 1.30/1.01  fd_cond:                                0
% 1.30/1.01  fd_pseudo_cond:                         1
% 1.30/1.01  ac_symbols:                             0
% 1.30/1.01  
% 1.30/1.01  ------ Propositional Solver
% 1.30/1.01  
% 1.30/1.01  prop_solver_calls:                      27
% 1.30/1.01  prop_fast_solver_calls:                 509
% 1.30/1.01  smt_solver_calls:                       0
% 1.30/1.01  smt_fast_solver_calls:                  0
% 1.30/1.01  prop_num_of_clauses:                    306
% 1.30/1.01  prop_preprocess_simplified:             1815
% 1.30/1.01  prop_fo_subsumed:                       7
% 1.30/1.01  prop_solver_time:                       0.
% 1.30/1.01  smt_solver_time:                        0.
% 1.30/1.01  smt_fast_solver_time:                   0.
% 1.30/1.01  prop_fast_solver_time:                  0.
% 1.30/1.01  prop_unsat_core_time:                   0.
% 1.30/1.01  
% 1.30/1.01  ------ QBF
% 1.30/1.01  
% 1.30/1.01  qbf_q_res:                              0
% 1.30/1.01  qbf_num_tautologies:                    0
% 1.30/1.01  qbf_prep_cycles:                        0
% 1.30/1.01  
% 1.30/1.01  ------ BMC1
% 1.30/1.01  
% 1.30/1.01  bmc1_current_bound:                     -1
% 1.30/1.01  bmc1_last_solved_bound:                 -1
% 1.30/1.01  bmc1_unsat_core_size:                   -1
% 1.30/1.01  bmc1_unsat_core_parents_size:           -1
% 1.30/1.01  bmc1_merge_next_fun:                    0
% 1.30/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.30/1.01  
% 1.30/1.01  ------ Instantiation
% 1.30/1.01  
% 1.30/1.01  inst_num_of_clauses:                    95
% 1.30/1.01  inst_num_in_passive:                    20
% 1.30/1.01  inst_num_in_active:                     67
% 1.30/1.01  inst_num_in_unprocessed:                9
% 1.30/1.01  inst_num_of_loops:                      100
% 1.30/1.01  inst_num_of_learning_restarts:          0
% 1.30/1.01  inst_num_moves_active_passive:          29
% 1.30/1.01  inst_lit_activity:                      0
% 1.30/1.01  inst_lit_activity_moves:                0
% 1.30/1.01  inst_num_tautologies:                   0
% 1.30/1.01  inst_num_prop_implied:                  0
% 1.30/1.01  inst_num_existing_simplified:           0
% 1.30/1.01  inst_num_eq_res_simplified:             0
% 1.30/1.01  inst_num_child_elim:                    0
% 1.30/1.01  inst_num_of_dismatching_blockings:      15
% 1.30/1.01  inst_num_of_non_proper_insts:           103
% 1.30/1.01  inst_num_of_duplicates:                 0
% 1.30/1.01  inst_inst_num_from_inst_to_res:         0
% 1.30/1.01  inst_dismatching_checking_time:         0.
% 1.30/1.01  
% 1.30/1.01  ------ Resolution
% 1.30/1.01  
% 1.30/1.01  res_num_of_clauses:                     0
% 1.30/1.01  res_num_in_passive:                     0
% 1.30/1.01  res_num_in_active:                      0
% 1.30/1.01  res_num_of_loops:                       90
% 1.30/1.01  res_forward_subset_subsumed:            28
% 1.30/1.01  res_backward_subset_subsumed:           2
% 1.30/1.01  res_forward_subsumed:                   0
% 1.30/1.01  res_backward_subsumed:                  0
% 1.30/1.01  res_forward_subsumption_resolution:     0
% 1.30/1.01  res_backward_subsumption_resolution:    0
% 1.30/1.01  res_clause_to_clause_subsumption:       28
% 1.30/1.01  res_orphan_elimination:                 0
% 1.30/1.01  res_tautology_del:                      23
% 1.30/1.01  res_num_eq_res_simplified:              1
% 1.30/1.01  res_num_sel_changes:                    0
% 1.30/1.01  res_moves_from_active_to_pass:          0
% 1.30/1.01  
% 1.30/1.01  ------ Superposition
% 1.30/1.01  
% 1.30/1.01  sup_time_total:                         0.
% 1.30/1.01  sup_time_generating:                    0.
% 1.30/1.01  sup_time_sim_full:                      0.
% 1.30/1.01  sup_time_sim_immed:                     0.
% 1.30/1.01  
% 1.30/1.01  sup_num_of_clauses:                     11
% 1.30/1.01  sup_num_in_active:                      9
% 1.30/1.01  sup_num_in_passive:                     2
% 1.30/1.01  sup_num_of_loops:                       19
% 1.30/1.01  sup_fw_superposition:                   4
% 1.30/1.01  sup_bw_superposition:                   0
% 1.30/1.01  sup_immediate_simplified:               2
% 1.30/1.01  sup_given_eliminated:                   0
% 1.30/1.01  comparisons_done:                       0
% 1.30/1.01  comparisons_avoided:                    0
% 1.30/1.01  
% 1.30/1.01  ------ Simplifications
% 1.30/1.01  
% 1.30/1.01  
% 1.30/1.01  sim_fw_subset_subsumed:                 0
% 1.30/1.01  sim_bw_subset_subsumed:                 0
% 1.30/1.01  sim_fw_subsumed:                        0
% 1.30/1.01  sim_bw_subsumed:                        0
% 1.30/1.01  sim_fw_subsumption_res:                 0
% 1.30/1.01  sim_bw_subsumption_res:                 0
% 1.30/1.01  sim_tautology_del:                      1
% 1.30/1.01  sim_eq_tautology_del:                   3
% 1.30/1.01  sim_eq_res_simp:                        1
% 1.30/1.01  sim_fw_demodulated:                     1
% 1.30/1.01  sim_bw_demodulated:                     11
% 1.30/1.01  sim_light_normalised:                   1
% 1.30/1.01  sim_joinable_taut:                      0
% 1.30/1.01  sim_joinable_simp:                      0
% 1.30/1.01  sim_ac_normalised:                      0
% 1.30/1.01  sim_smt_subsumption:                    0
% 1.30/1.01  
%------------------------------------------------------------------------------
