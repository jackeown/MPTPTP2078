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
% DateTime   : Thu Dec  3 12:00:57 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  223 (11576 expanded)
%              Number of clauses        :  154 (4011 expanded)
%              Number of leaves         :   22 (2592 expanded)
%              Depth                    :   28
%              Number of atoms          :  656 (48223 expanded)
%              Number of equality atoms :  365 (14762 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f37,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK4(X3)) = X3
        & r2_hidden(sK4(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK1,sK2,sK3) != sK2
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK3,X4) = X3
              & r2_hidden(X4,sK1) )
          | ~ r2_hidden(X3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_relset_1(sK1,sK2,sK3) != sK2
    & ! [X3] :
        ( ( k1_funct_1(sK3,sK4(X3)) = X3
          & r2_hidden(sK4(X3),sK1) )
        | ~ r2_hidden(X3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f39,f38])).

fof(f67,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,sK4(X3)) = X3
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    & k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X3] :
      ( r2_hidden(sK4(X3),sK1)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_396,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_398,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_28])).

cnf(c_922,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_926,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1461,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_922,c_926])).

cnf(c_1536,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_398,c_1461])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_936,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(sK3,sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_924,plain,
    ( k1_funct_1(sK3,sK4(X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1619,plain,
    ( k1_funct_1(sK3,sK4(sK0(sK2,X0))) = sK0(sK2,X0)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_924])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_925,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1404,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_922,c_925])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_927,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1593,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_927])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2015,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1593,c_33])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_932,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2344,plain,
    ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2015,c_932])).

cnf(c_2918,plain,
    ( r2_hidden(sK0(k2_relat_1(sK3),X0),sK2) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_936,c_2344])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_937,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3092,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_937])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_934,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3974,plain,
    ( k2_relat_1(sK3) = sK2
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_934])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1141,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_560,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1125,plain,
    ( k2_relset_1(sK1,sK2,sK3) != X0
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1334,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK1,sK2,sK3) = sK2
    | sK2 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_1172,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1521,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(sK2,k2_relat_1(sK3))
    | sK2 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_1522,plain,
    ( sK2 = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1521])).

cnf(c_3982,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3974,c_28,c_25,c_1141,c_1334,c_1522,c_3092])).

cnf(c_3987,plain,
    ( k1_funct_1(sK3,sK4(sK0(sK2,k2_relat_1(sK3)))) = sK0(sK2,k2_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_1619,c_3982])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_312,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_921,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_935,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1748,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),X1) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_935])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1212,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_1213,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1212])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1232,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1233,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_3386,plain,
    ( r1_tarski(sK3,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1748,c_33,c_1213,c_1233])).

cnf(c_3387,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),X1) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3386])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_929,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3396,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3387,c_929])).

cnf(c_10246,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_3396])).

cnf(c_10287,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3987,c_10246])).

cnf(c_2372,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_929])).

cnf(c_2623,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2372,c_33,c_1213,c_1233])).

cnf(c_2624,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2623])).

cnf(c_4202,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3987,c_2624])).

cnf(c_2877,plain,
    ( ~ r2_hidden(sK0(X0,k2_relat_1(sK3)),k2_relat_1(sK3))
    | r1_tarski(X0,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4870,plain,
    ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3))
    | r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2877])).

cnf(c_4871,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4870])).

cnf(c_19538,plain,
    ( r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10287,c_28,c_25,c_1141,c_1334,c_1522,c_3092,c_4202,c_4871])).

cnf(c_19546,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_19538])).

cnf(c_2876,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK3)),X0)
    | r1_tarski(X0,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5114,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
    | r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2876])).

cnf(c_5115,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) = iProver_top
    | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5114])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(sK4(X0),sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10028,plain,
    ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_10029,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) != iProver_top
    | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10028])).

cnf(c_19719,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19546,c_28,c_25,c_1141,c_1334,c_1522,c_3092,c_5115,c_10029])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK2 != k1_xboole_0
    | sK1 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_363,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_919,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_19857,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19719,c_919])).

cnf(c_19879,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_19857])).

cnf(c_19862,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19719,c_922])).

cnf(c_19883,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19879,c_19862])).

cnf(c_364,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_559,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1183,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1128,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1209,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_1210,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_1176,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1520,plain,
    ( k2_relat_1(sK3) != X0
    | sK2 != X0
    | sK2 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_1959,plain,
    ( k2_relat_1(sK3) != k2_relat_1(X0)
    | sK2 != k2_relat_1(X0)
    | sK2 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_1961,plain,
    ( k2_relat_1(sK3) != k2_relat_1(k1_xboole_0)
    | sK2 = k2_relat_1(sK3)
    | sK2 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1959])).

cnf(c_566,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_1960,plain,
    ( k2_relat_1(sK3) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_1962,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_1393,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_2243,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_2244,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2243])).

cnf(c_6930,plain,
    ( k2_relat_1(X0) != X1
    | sK2 != X1
    | sK2 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_6931,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | sK2 = k2_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6930])).

cnf(c_24795,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19883,c_28,c_25,c_11,c_364,c_1141,c_1183,c_1209,c_1210,c_1334,c_1522,c_1961,c_1962,c_2244,c_3092,c_5115,c_6931,c_10029,c_19546,c_19862])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_923,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4(X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1747,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4(X0),X1) = iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_935])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_928,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3397,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK3,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3387,c_928])).

cnf(c_8956,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4(X0),k1_relat_1(X1)) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_3397])).

cnf(c_9318,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK4(X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_8956])).

cnf(c_19775,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK4(X0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19719,c_9318])).

cnf(c_19543,plain,
    ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) != iProver_top
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_19538])).

cnf(c_21924,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19775,c_28,c_25,c_1141,c_1334,c_1522,c_3092,c_5115,c_19543])).

cnf(c_24804,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24795,c_21924])).

cnf(c_19854,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_19719,c_1461])).

cnf(c_24807,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_24795,c_19854])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK2 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_918,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_19858,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19719,c_918])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_88,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_92,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_562,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1292,plain,
    ( X0 != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_1648,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_1650,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_565,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_1649,plain,
    ( X0 != sK2
    | X1 != sK1
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_1651,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_1838,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1839,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_21008,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19858])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3507,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_6316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_3507])).

cnf(c_17720,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X0 != sK3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6316])).

cnf(c_21509,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_17720])).

cnf(c_21511,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_21509])).

cnf(c_22403,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_19858,c_28,c_25,c_11,c_88,c_92,c_364,c_1141,c_1183,c_1209,c_1210,c_1334,c_1522,c_1650,c_1651,c_1839,c_1961,c_1962,c_2244,c_3092,c_5115,c_6931,c_10029,c_19546,c_21008,c_19862,c_21511])).

cnf(c_24818,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_24807,c_22403])).

cnf(c_24828,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24804,c_24818])).

cnf(c_87,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_89,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24828,c_89])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:12:29 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 7.56/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/1.47  
% 7.56/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.56/1.47  
% 7.56/1.47  ------  iProver source info
% 7.56/1.47  
% 7.56/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.56/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.56/1.47  git: non_committed_changes: false
% 7.56/1.47  git: last_make_outside_of_git: false
% 7.56/1.47  
% 7.56/1.47  ------ 
% 7.56/1.47  
% 7.56/1.47  ------ Input Options
% 7.56/1.47  
% 7.56/1.47  --out_options                           all
% 7.56/1.47  --tptp_safe_out                         true
% 7.56/1.47  --problem_path                          ""
% 7.56/1.47  --include_path                          ""
% 7.56/1.47  --clausifier                            res/vclausify_rel
% 7.56/1.47  --clausifier_options                    --mode clausify
% 7.56/1.47  --stdin                                 false
% 7.56/1.47  --stats_out                             all
% 7.56/1.47  
% 7.56/1.47  ------ General Options
% 7.56/1.47  
% 7.56/1.47  --fof                                   false
% 7.56/1.47  --time_out_real                         305.
% 7.56/1.47  --time_out_virtual                      -1.
% 7.56/1.47  --symbol_type_check                     false
% 7.56/1.47  --clausify_out                          false
% 7.56/1.47  --sig_cnt_out                           false
% 7.56/1.47  --trig_cnt_out                          false
% 7.56/1.47  --trig_cnt_out_tolerance                1.
% 7.56/1.47  --trig_cnt_out_sk_spl                   false
% 7.56/1.47  --abstr_cl_out                          false
% 7.56/1.47  
% 7.56/1.47  ------ Global Options
% 7.56/1.47  
% 7.56/1.47  --schedule                              default
% 7.56/1.47  --add_important_lit                     false
% 7.56/1.47  --prop_solver_per_cl                    1000
% 7.56/1.47  --min_unsat_core                        false
% 7.56/1.47  --soft_assumptions                      false
% 7.56/1.47  --soft_lemma_size                       3
% 7.56/1.47  --prop_impl_unit_size                   0
% 7.56/1.47  --prop_impl_unit                        []
% 7.56/1.47  --share_sel_clauses                     true
% 7.56/1.47  --reset_solvers                         false
% 7.56/1.47  --bc_imp_inh                            [conj_cone]
% 7.56/1.47  --conj_cone_tolerance                   3.
% 7.56/1.47  --extra_neg_conj                        none
% 7.56/1.47  --large_theory_mode                     true
% 7.56/1.47  --prolific_symb_bound                   200
% 7.56/1.47  --lt_threshold                          2000
% 7.56/1.47  --clause_weak_htbl                      true
% 7.56/1.47  --gc_record_bc_elim                     false
% 7.56/1.47  
% 7.56/1.47  ------ Preprocessing Options
% 7.56/1.47  
% 7.56/1.47  --preprocessing_flag                    true
% 7.56/1.47  --time_out_prep_mult                    0.1
% 7.56/1.47  --splitting_mode                        input
% 7.56/1.47  --splitting_grd                         true
% 7.56/1.47  --splitting_cvd                         false
% 7.56/1.47  --splitting_cvd_svl                     false
% 7.56/1.47  --splitting_nvd                         32
% 7.56/1.47  --sub_typing                            true
% 7.56/1.47  --prep_gs_sim                           true
% 7.56/1.47  --prep_unflatten                        true
% 7.56/1.47  --prep_res_sim                          true
% 7.56/1.47  --prep_upred                            true
% 7.56/1.47  --prep_sem_filter                       exhaustive
% 7.56/1.47  --prep_sem_filter_out                   false
% 7.56/1.47  --pred_elim                             true
% 7.56/1.47  --res_sim_input                         true
% 7.56/1.47  --eq_ax_congr_red                       true
% 7.56/1.47  --pure_diseq_elim                       true
% 7.56/1.47  --brand_transform                       false
% 7.56/1.47  --non_eq_to_eq                          false
% 7.56/1.47  --prep_def_merge                        true
% 7.56/1.47  --prep_def_merge_prop_impl              false
% 7.56/1.47  --prep_def_merge_mbd                    true
% 7.56/1.47  --prep_def_merge_tr_red                 false
% 7.56/1.47  --prep_def_merge_tr_cl                  false
% 7.56/1.47  --smt_preprocessing                     true
% 7.56/1.47  --smt_ac_axioms                         fast
% 7.56/1.47  --preprocessed_out                      false
% 7.56/1.47  --preprocessed_stats                    false
% 7.56/1.47  
% 7.56/1.47  ------ Abstraction refinement Options
% 7.56/1.47  
% 7.56/1.47  --abstr_ref                             []
% 7.56/1.47  --abstr_ref_prep                        false
% 7.56/1.47  --abstr_ref_until_sat                   false
% 7.56/1.47  --abstr_ref_sig_restrict                funpre
% 7.56/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.56/1.47  --abstr_ref_under                       []
% 7.56/1.47  
% 7.56/1.47  ------ SAT Options
% 7.56/1.47  
% 7.56/1.47  --sat_mode                              false
% 7.56/1.47  --sat_fm_restart_options                ""
% 7.56/1.47  --sat_gr_def                            false
% 7.56/1.47  --sat_epr_types                         true
% 7.56/1.47  --sat_non_cyclic_types                  false
% 7.56/1.47  --sat_finite_models                     false
% 7.56/1.47  --sat_fm_lemmas                         false
% 7.56/1.47  --sat_fm_prep                           false
% 7.56/1.47  --sat_fm_uc_incr                        true
% 7.56/1.47  --sat_out_model                         small
% 7.56/1.47  --sat_out_clauses                       false
% 7.56/1.47  
% 7.56/1.47  ------ QBF Options
% 7.56/1.47  
% 7.56/1.47  --qbf_mode                              false
% 7.56/1.47  --qbf_elim_univ                         false
% 7.56/1.47  --qbf_dom_inst                          none
% 7.56/1.47  --qbf_dom_pre_inst                      false
% 7.56/1.47  --qbf_sk_in                             false
% 7.56/1.47  --qbf_pred_elim                         true
% 7.56/1.47  --qbf_split                             512
% 7.56/1.47  
% 7.56/1.47  ------ BMC1 Options
% 7.56/1.47  
% 7.56/1.47  --bmc1_incremental                      false
% 7.56/1.47  --bmc1_axioms                           reachable_all
% 7.56/1.47  --bmc1_min_bound                        0
% 7.56/1.47  --bmc1_max_bound                        -1
% 7.56/1.47  --bmc1_max_bound_default                -1
% 7.56/1.47  --bmc1_symbol_reachability              true
% 7.56/1.47  --bmc1_property_lemmas                  false
% 7.56/1.47  --bmc1_k_induction                      false
% 7.56/1.47  --bmc1_non_equiv_states                 false
% 7.56/1.47  --bmc1_deadlock                         false
% 7.56/1.47  --bmc1_ucm                              false
% 7.56/1.47  --bmc1_add_unsat_core                   none
% 7.56/1.47  --bmc1_unsat_core_children              false
% 7.56/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.56/1.47  --bmc1_out_stat                         full
% 7.56/1.47  --bmc1_ground_init                      false
% 7.56/1.47  --bmc1_pre_inst_next_state              false
% 7.56/1.47  --bmc1_pre_inst_state                   false
% 7.56/1.47  --bmc1_pre_inst_reach_state             false
% 7.56/1.47  --bmc1_out_unsat_core                   false
% 7.56/1.47  --bmc1_aig_witness_out                  false
% 7.56/1.47  --bmc1_verbose                          false
% 7.56/1.47  --bmc1_dump_clauses_tptp                false
% 7.56/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.56/1.47  --bmc1_dump_file                        -
% 7.56/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.56/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.56/1.47  --bmc1_ucm_extend_mode                  1
% 7.56/1.47  --bmc1_ucm_init_mode                    2
% 7.56/1.47  --bmc1_ucm_cone_mode                    none
% 7.56/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.56/1.47  --bmc1_ucm_relax_model                  4
% 7.56/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.56/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.56/1.47  --bmc1_ucm_layered_model                none
% 7.56/1.47  --bmc1_ucm_max_lemma_size               10
% 7.56/1.47  
% 7.56/1.47  ------ AIG Options
% 7.56/1.47  
% 7.56/1.47  --aig_mode                              false
% 7.56/1.47  
% 7.56/1.47  ------ Instantiation Options
% 7.56/1.47  
% 7.56/1.47  --instantiation_flag                    true
% 7.56/1.47  --inst_sos_flag                         false
% 7.56/1.47  --inst_sos_phase                        true
% 7.56/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.56/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.56/1.47  --inst_lit_sel_side                     num_symb
% 7.56/1.47  --inst_solver_per_active                1400
% 7.56/1.47  --inst_solver_calls_frac                1.
% 7.56/1.47  --inst_passive_queue_type               priority_queues
% 7.56/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.56/1.47  --inst_passive_queues_freq              [25;2]
% 7.56/1.47  --inst_dismatching                      true
% 7.56/1.47  --inst_eager_unprocessed_to_passive     true
% 7.56/1.47  --inst_prop_sim_given                   true
% 7.56/1.47  --inst_prop_sim_new                     false
% 7.56/1.47  --inst_subs_new                         false
% 7.56/1.47  --inst_eq_res_simp                      false
% 7.56/1.47  --inst_subs_given                       false
% 7.56/1.47  --inst_orphan_elimination               true
% 7.56/1.47  --inst_learning_loop_flag               true
% 7.56/1.47  --inst_learning_start                   3000
% 7.56/1.47  --inst_learning_factor                  2
% 7.56/1.47  --inst_start_prop_sim_after_learn       3
% 7.56/1.47  --inst_sel_renew                        solver
% 7.56/1.47  --inst_lit_activity_flag                true
% 7.56/1.47  --inst_restr_to_given                   false
% 7.56/1.47  --inst_activity_threshold               500
% 7.56/1.47  --inst_out_proof                        true
% 7.56/1.47  
% 7.56/1.47  ------ Resolution Options
% 7.56/1.47  
% 7.56/1.47  --resolution_flag                       true
% 7.56/1.47  --res_lit_sel                           adaptive
% 7.56/1.47  --res_lit_sel_side                      none
% 7.56/1.47  --res_ordering                          kbo
% 7.56/1.47  --res_to_prop_solver                    active
% 7.56/1.47  --res_prop_simpl_new                    false
% 7.56/1.47  --res_prop_simpl_given                  true
% 7.56/1.47  --res_passive_queue_type                priority_queues
% 7.56/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.56/1.47  --res_passive_queues_freq               [15;5]
% 7.56/1.47  --res_forward_subs                      full
% 7.56/1.47  --res_backward_subs                     full
% 7.56/1.47  --res_forward_subs_resolution           true
% 7.56/1.47  --res_backward_subs_resolution          true
% 7.56/1.47  --res_orphan_elimination                true
% 7.56/1.47  --res_time_limit                        2.
% 7.56/1.47  --res_out_proof                         true
% 7.56/1.47  
% 7.56/1.47  ------ Superposition Options
% 7.56/1.47  
% 7.56/1.47  --superposition_flag                    true
% 7.56/1.47  --sup_passive_queue_type                priority_queues
% 7.56/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.56/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.56/1.47  --demod_completeness_check              fast
% 7.56/1.47  --demod_use_ground                      true
% 7.56/1.47  --sup_to_prop_solver                    passive
% 7.56/1.47  --sup_prop_simpl_new                    true
% 7.56/1.47  --sup_prop_simpl_given                  true
% 7.56/1.47  --sup_fun_splitting                     false
% 7.56/1.47  --sup_smt_interval                      50000
% 7.56/1.47  
% 7.56/1.47  ------ Superposition Simplification Setup
% 7.56/1.47  
% 7.56/1.47  --sup_indices_passive                   []
% 7.56/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.56/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.47  --sup_full_bw                           [BwDemod]
% 7.56/1.47  --sup_immed_triv                        [TrivRules]
% 7.56/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.47  --sup_immed_bw_main                     []
% 7.56/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.56/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.56/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.56/1.47  
% 7.56/1.47  ------ Combination Options
% 7.56/1.47  
% 7.56/1.47  --comb_res_mult                         3
% 7.56/1.47  --comb_sup_mult                         2
% 7.56/1.47  --comb_inst_mult                        10
% 7.56/1.47  
% 7.56/1.47  ------ Debug Options
% 7.56/1.47  
% 7.56/1.47  --dbg_backtrace                         false
% 7.56/1.47  --dbg_dump_prop_clauses                 false
% 7.56/1.47  --dbg_dump_prop_clauses_file            -
% 7.56/1.47  --dbg_out_stat                          false
% 7.56/1.47  ------ Parsing...
% 7.56/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.56/1.47  
% 7.56/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.56/1.47  
% 7.56/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.56/1.47  
% 7.56/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.47  ------ Proving...
% 7.56/1.47  ------ Problem Properties 
% 7.56/1.47  
% 7.56/1.47  
% 7.56/1.47  clauses                                 24
% 7.56/1.47  conjectures                             4
% 7.56/1.47  EPR                                     3
% 7.56/1.47  Horn                                    21
% 7.56/1.47  unary                                   6
% 7.56/1.47  binary                                  8
% 7.56/1.47  lits                                    53
% 7.56/1.47  lits eq                                 15
% 7.56/1.47  fd_pure                                 0
% 7.56/1.47  fd_pseudo                               0
% 7.56/1.47  fd_cond                                 0
% 7.56/1.47  fd_pseudo_cond                          2
% 7.56/1.47  AC symbols                              0
% 7.56/1.47  
% 7.56/1.47  ------ Schedule dynamic 5 is on 
% 7.56/1.47  
% 7.56/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.56/1.47  
% 7.56/1.47  
% 7.56/1.47  ------ 
% 7.56/1.47  Current options:
% 7.56/1.47  ------ 
% 7.56/1.47  
% 7.56/1.47  ------ Input Options
% 7.56/1.47  
% 7.56/1.47  --out_options                           all
% 7.56/1.47  --tptp_safe_out                         true
% 7.56/1.47  --problem_path                          ""
% 7.56/1.47  --include_path                          ""
% 7.56/1.47  --clausifier                            res/vclausify_rel
% 7.56/1.47  --clausifier_options                    --mode clausify
% 7.56/1.47  --stdin                                 false
% 7.56/1.47  --stats_out                             all
% 7.56/1.47  
% 7.56/1.47  ------ General Options
% 7.56/1.47  
% 7.56/1.47  --fof                                   false
% 7.56/1.47  --time_out_real                         305.
% 7.56/1.47  --time_out_virtual                      -1.
% 7.56/1.47  --symbol_type_check                     false
% 7.56/1.47  --clausify_out                          false
% 7.56/1.47  --sig_cnt_out                           false
% 7.56/1.47  --trig_cnt_out                          false
% 7.56/1.47  --trig_cnt_out_tolerance                1.
% 7.56/1.47  --trig_cnt_out_sk_spl                   false
% 7.56/1.47  --abstr_cl_out                          false
% 7.56/1.47  
% 7.56/1.47  ------ Global Options
% 7.56/1.47  
% 7.56/1.47  --schedule                              default
% 7.56/1.47  --add_important_lit                     false
% 7.56/1.47  --prop_solver_per_cl                    1000
% 7.56/1.47  --min_unsat_core                        false
% 7.56/1.47  --soft_assumptions                      false
% 7.56/1.47  --soft_lemma_size                       3
% 7.56/1.47  --prop_impl_unit_size                   0
% 7.56/1.47  --prop_impl_unit                        []
% 7.56/1.47  --share_sel_clauses                     true
% 7.56/1.47  --reset_solvers                         false
% 7.56/1.47  --bc_imp_inh                            [conj_cone]
% 7.56/1.47  --conj_cone_tolerance                   3.
% 7.56/1.47  --extra_neg_conj                        none
% 7.56/1.47  --large_theory_mode                     true
% 7.56/1.47  --prolific_symb_bound                   200
% 7.56/1.47  --lt_threshold                          2000
% 7.56/1.47  --clause_weak_htbl                      true
% 7.56/1.47  --gc_record_bc_elim                     false
% 7.56/1.47  
% 7.56/1.47  ------ Preprocessing Options
% 7.56/1.47  
% 7.56/1.47  --preprocessing_flag                    true
% 7.56/1.47  --time_out_prep_mult                    0.1
% 7.56/1.47  --splitting_mode                        input
% 7.56/1.47  --splitting_grd                         true
% 7.56/1.47  --splitting_cvd                         false
% 7.56/1.47  --splitting_cvd_svl                     false
% 7.56/1.47  --splitting_nvd                         32
% 7.56/1.47  --sub_typing                            true
% 7.56/1.47  --prep_gs_sim                           true
% 7.56/1.47  --prep_unflatten                        true
% 7.56/1.47  --prep_res_sim                          true
% 7.56/1.47  --prep_upred                            true
% 7.56/1.47  --prep_sem_filter                       exhaustive
% 7.56/1.47  --prep_sem_filter_out                   false
% 7.56/1.47  --pred_elim                             true
% 7.56/1.47  --res_sim_input                         true
% 7.56/1.47  --eq_ax_congr_red                       true
% 7.56/1.47  --pure_diseq_elim                       true
% 7.56/1.47  --brand_transform                       false
% 7.56/1.47  --non_eq_to_eq                          false
% 7.56/1.47  --prep_def_merge                        true
% 7.56/1.47  --prep_def_merge_prop_impl              false
% 7.56/1.47  --prep_def_merge_mbd                    true
% 7.56/1.47  --prep_def_merge_tr_red                 false
% 7.56/1.47  --prep_def_merge_tr_cl                  false
% 7.56/1.47  --smt_preprocessing                     true
% 7.56/1.47  --smt_ac_axioms                         fast
% 7.56/1.47  --preprocessed_out                      false
% 7.56/1.47  --preprocessed_stats                    false
% 7.56/1.47  
% 7.56/1.47  ------ Abstraction refinement Options
% 7.56/1.47  
% 7.56/1.47  --abstr_ref                             []
% 7.56/1.47  --abstr_ref_prep                        false
% 7.56/1.47  --abstr_ref_until_sat                   false
% 7.56/1.47  --abstr_ref_sig_restrict                funpre
% 7.56/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.56/1.47  --abstr_ref_under                       []
% 7.56/1.47  
% 7.56/1.47  ------ SAT Options
% 7.56/1.47  
% 7.56/1.47  --sat_mode                              false
% 7.56/1.47  --sat_fm_restart_options                ""
% 7.56/1.47  --sat_gr_def                            false
% 7.56/1.47  --sat_epr_types                         true
% 7.56/1.47  --sat_non_cyclic_types                  false
% 7.56/1.47  --sat_finite_models                     false
% 7.56/1.47  --sat_fm_lemmas                         false
% 7.56/1.47  --sat_fm_prep                           false
% 7.56/1.47  --sat_fm_uc_incr                        true
% 7.56/1.47  --sat_out_model                         small
% 7.56/1.47  --sat_out_clauses                       false
% 7.56/1.47  
% 7.56/1.47  ------ QBF Options
% 7.56/1.47  
% 7.56/1.47  --qbf_mode                              false
% 7.56/1.47  --qbf_elim_univ                         false
% 7.56/1.47  --qbf_dom_inst                          none
% 7.56/1.47  --qbf_dom_pre_inst                      false
% 7.56/1.47  --qbf_sk_in                             false
% 7.56/1.47  --qbf_pred_elim                         true
% 7.56/1.47  --qbf_split                             512
% 7.56/1.47  
% 7.56/1.47  ------ BMC1 Options
% 7.56/1.47  
% 7.56/1.47  --bmc1_incremental                      false
% 7.56/1.47  --bmc1_axioms                           reachable_all
% 7.56/1.47  --bmc1_min_bound                        0
% 7.56/1.47  --bmc1_max_bound                        -1
% 7.56/1.47  --bmc1_max_bound_default                -1
% 7.56/1.47  --bmc1_symbol_reachability              true
% 7.56/1.47  --bmc1_property_lemmas                  false
% 7.56/1.47  --bmc1_k_induction                      false
% 7.56/1.47  --bmc1_non_equiv_states                 false
% 7.56/1.47  --bmc1_deadlock                         false
% 7.56/1.47  --bmc1_ucm                              false
% 7.56/1.47  --bmc1_add_unsat_core                   none
% 7.56/1.47  --bmc1_unsat_core_children              false
% 7.56/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.56/1.47  --bmc1_out_stat                         full
% 7.56/1.47  --bmc1_ground_init                      false
% 7.56/1.47  --bmc1_pre_inst_next_state              false
% 7.56/1.47  --bmc1_pre_inst_state                   false
% 7.56/1.47  --bmc1_pre_inst_reach_state             false
% 7.56/1.47  --bmc1_out_unsat_core                   false
% 7.56/1.47  --bmc1_aig_witness_out                  false
% 7.56/1.47  --bmc1_verbose                          false
% 7.56/1.47  --bmc1_dump_clauses_tptp                false
% 7.56/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.56/1.47  --bmc1_dump_file                        -
% 7.56/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.56/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.56/1.47  --bmc1_ucm_extend_mode                  1
% 7.56/1.47  --bmc1_ucm_init_mode                    2
% 7.56/1.47  --bmc1_ucm_cone_mode                    none
% 7.56/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.56/1.47  --bmc1_ucm_relax_model                  4
% 7.56/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.56/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.56/1.47  --bmc1_ucm_layered_model                none
% 7.56/1.47  --bmc1_ucm_max_lemma_size               10
% 7.56/1.47  
% 7.56/1.47  ------ AIG Options
% 7.56/1.47  
% 7.56/1.47  --aig_mode                              false
% 7.56/1.47  
% 7.56/1.47  ------ Instantiation Options
% 7.56/1.47  
% 7.56/1.47  --instantiation_flag                    true
% 7.56/1.47  --inst_sos_flag                         false
% 7.56/1.47  --inst_sos_phase                        true
% 7.56/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.56/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.56/1.47  --inst_lit_sel_side                     none
% 7.56/1.47  --inst_solver_per_active                1400
% 7.56/1.47  --inst_solver_calls_frac                1.
% 7.56/1.47  --inst_passive_queue_type               priority_queues
% 7.56/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.56/1.47  --inst_passive_queues_freq              [25;2]
% 7.56/1.47  --inst_dismatching                      true
% 7.56/1.47  --inst_eager_unprocessed_to_passive     true
% 7.56/1.47  --inst_prop_sim_given                   true
% 7.56/1.47  --inst_prop_sim_new                     false
% 7.56/1.47  --inst_subs_new                         false
% 7.56/1.47  --inst_eq_res_simp                      false
% 7.56/1.47  --inst_subs_given                       false
% 7.56/1.47  --inst_orphan_elimination               true
% 7.56/1.47  --inst_learning_loop_flag               true
% 7.56/1.47  --inst_learning_start                   3000
% 7.56/1.47  --inst_learning_factor                  2
% 7.56/1.47  --inst_start_prop_sim_after_learn       3
% 7.56/1.47  --inst_sel_renew                        solver
% 7.56/1.47  --inst_lit_activity_flag                true
% 7.56/1.47  --inst_restr_to_given                   false
% 7.56/1.47  --inst_activity_threshold               500
% 7.56/1.47  --inst_out_proof                        true
% 7.56/1.47  
% 7.56/1.47  ------ Resolution Options
% 7.56/1.47  
% 7.56/1.47  --resolution_flag                       false
% 7.56/1.47  --res_lit_sel                           adaptive
% 7.56/1.47  --res_lit_sel_side                      none
% 7.56/1.47  --res_ordering                          kbo
% 7.56/1.47  --res_to_prop_solver                    active
% 7.56/1.47  --res_prop_simpl_new                    false
% 7.56/1.47  --res_prop_simpl_given                  true
% 7.56/1.47  --res_passive_queue_type                priority_queues
% 7.56/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.56/1.47  --res_passive_queues_freq               [15;5]
% 7.56/1.47  --res_forward_subs                      full
% 7.56/1.47  --res_backward_subs                     full
% 7.56/1.47  --res_forward_subs_resolution           true
% 7.56/1.47  --res_backward_subs_resolution          true
% 7.56/1.47  --res_orphan_elimination                true
% 7.56/1.47  --res_time_limit                        2.
% 7.56/1.47  --res_out_proof                         true
% 7.56/1.47  
% 7.56/1.47  ------ Superposition Options
% 7.56/1.47  
% 7.56/1.47  --superposition_flag                    true
% 7.56/1.47  --sup_passive_queue_type                priority_queues
% 7.56/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.56/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.56/1.47  --demod_completeness_check              fast
% 7.56/1.47  --demod_use_ground                      true
% 7.56/1.47  --sup_to_prop_solver                    passive
% 7.56/1.47  --sup_prop_simpl_new                    true
% 7.56/1.47  --sup_prop_simpl_given                  true
% 7.56/1.47  --sup_fun_splitting                     false
% 7.56/1.47  --sup_smt_interval                      50000
% 7.56/1.47  
% 7.56/1.47  ------ Superposition Simplification Setup
% 7.56/1.47  
% 7.56/1.47  --sup_indices_passive                   []
% 7.56/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.56/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.47  --sup_full_bw                           [BwDemod]
% 7.56/1.47  --sup_immed_triv                        [TrivRules]
% 7.56/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.47  --sup_immed_bw_main                     []
% 7.56/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.56/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.56/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.56/1.47  
% 7.56/1.47  ------ Combination Options
% 7.56/1.47  
% 7.56/1.47  --comb_res_mult                         3
% 7.56/1.47  --comb_sup_mult                         2
% 7.56/1.47  --comb_inst_mult                        10
% 7.56/1.47  
% 7.56/1.47  ------ Debug Options
% 7.56/1.47  
% 7.56/1.47  --dbg_backtrace                         false
% 7.56/1.47  --dbg_dump_prop_clauses                 false
% 7.56/1.47  --dbg_dump_prop_clauses_file            -
% 7.56/1.47  --dbg_out_stat                          false
% 7.56/1.47  
% 7.56/1.47  
% 7.56/1.47  
% 7.56/1.47  
% 7.56/1.47  ------ Proving...
% 7.56/1.47  
% 7.56/1.47  
% 7.56/1.47  % SZS status Theorem for theBenchmark.p
% 7.56/1.47  
% 7.56/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.56/1.47  
% 7.56/1.47  fof(f12,axiom,(
% 7.56/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f25,plain,(
% 7.56/1.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.47    inference(ennf_transformation,[],[f12])).
% 7.56/1.47  
% 7.56/1.47  fof(f26,plain,(
% 7.56/1.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.47    inference(flattening,[],[f25])).
% 7.56/1.47  
% 7.56/1.47  fof(f37,plain,(
% 7.56/1.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.47    inference(nnf_transformation,[],[f26])).
% 7.56/1.47  
% 7.56/1.47  fof(f60,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.56/1.47    inference(cnf_transformation,[],[f37])).
% 7.56/1.47  
% 7.56/1.47  fof(f13,conjecture,(
% 7.56/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f14,negated_conjecture,(
% 7.56/1.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 7.56/1.47    inference(negated_conjecture,[],[f13])).
% 7.56/1.47  
% 7.56/1.47  fof(f27,plain,(
% 7.56/1.47    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.56/1.47    inference(ennf_transformation,[],[f14])).
% 7.56/1.47  
% 7.56/1.47  fof(f28,plain,(
% 7.56/1.47    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.56/1.47    inference(flattening,[],[f27])).
% 7.56/1.47  
% 7.56/1.47  fof(f39,plain,(
% 7.56/1.47    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK4(X3)) = X3 & r2_hidden(sK4(X3),X0)))) )),
% 7.56/1.47    introduced(choice_axiom,[])).
% 7.56/1.47  
% 7.56/1.47  fof(f38,plain,(
% 7.56/1.47    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : (? [X4] : (k1_funct_1(sK3,X4) = X3 & r2_hidden(X4,sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 7.56/1.47    introduced(choice_axiom,[])).
% 7.56/1.47  
% 7.56/1.47  fof(f40,plain,(
% 7.56/1.47    k2_relset_1(sK1,sK2,sK3) != sK2 & ! [X3] : ((k1_funct_1(sK3,sK4(X3)) = X3 & r2_hidden(sK4(X3),sK1)) | ~r2_hidden(X3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 7.56/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f28,f39,f38])).
% 7.56/1.47  
% 7.56/1.47  fof(f67,plain,(
% 7.56/1.47    v1_funct_2(sK3,sK1,sK2)),
% 7.56/1.47    inference(cnf_transformation,[],[f40])).
% 7.56/1.47  
% 7.56/1.47  fof(f68,plain,(
% 7.56/1.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.56/1.47    inference(cnf_transformation,[],[f40])).
% 7.56/1.47  
% 7.56/1.47  fof(f10,axiom,(
% 7.56/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f23,plain,(
% 7.56/1.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.47    inference(ennf_transformation,[],[f10])).
% 7.56/1.47  
% 7.56/1.47  fof(f58,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.56/1.47    inference(cnf_transformation,[],[f23])).
% 7.56/1.47  
% 7.56/1.47  fof(f1,axiom,(
% 7.56/1.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f15,plain,(
% 7.56/1.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.56/1.47    inference(ennf_transformation,[],[f1])).
% 7.56/1.47  
% 7.56/1.47  fof(f29,plain,(
% 7.56/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.56/1.47    inference(nnf_transformation,[],[f15])).
% 7.56/1.47  
% 7.56/1.47  fof(f30,plain,(
% 7.56/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.56/1.47    inference(rectify,[],[f29])).
% 7.56/1.47  
% 7.56/1.47  fof(f31,plain,(
% 7.56/1.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.56/1.47    introduced(choice_axiom,[])).
% 7.56/1.47  
% 7.56/1.47  fof(f32,plain,(
% 7.56/1.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.56/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.56/1.47  
% 7.56/1.47  fof(f42,plain,(
% 7.56/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f32])).
% 7.56/1.47  
% 7.56/1.47  fof(f70,plain,(
% 7.56/1.47    ( ! [X3] : (k1_funct_1(sK3,sK4(X3)) = X3 | ~r2_hidden(X3,sK2)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f40])).
% 7.56/1.47  
% 7.56/1.47  fof(f11,axiom,(
% 7.56/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f24,plain,(
% 7.56/1.47    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.47    inference(ennf_transformation,[],[f11])).
% 7.56/1.47  
% 7.56/1.47  fof(f59,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.56/1.47    inference(cnf_transformation,[],[f24])).
% 7.56/1.47  
% 7.56/1.47  fof(f9,axiom,(
% 7.56/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f22,plain,(
% 7.56/1.47    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.47    inference(ennf_transformation,[],[f9])).
% 7.56/1.47  
% 7.56/1.47  fof(f57,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.56/1.47    inference(cnf_transformation,[],[f22])).
% 7.56/1.47  
% 7.56/1.47  fof(f3,axiom,(
% 7.56/1.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f16,plain,(
% 7.56/1.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.56/1.47    inference(ennf_transformation,[],[f3])).
% 7.56/1.47  
% 7.56/1.47  fof(f47,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.56/1.47    inference(cnf_transformation,[],[f16])).
% 7.56/1.47  
% 7.56/1.47  fof(f43,plain,(
% 7.56/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f32])).
% 7.56/1.47  
% 7.56/1.47  fof(f2,axiom,(
% 7.56/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f33,plain,(
% 7.56/1.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.56/1.47    inference(nnf_transformation,[],[f2])).
% 7.56/1.47  
% 7.56/1.47  fof(f34,plain,(
% 7.56/1.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.56/1.47    inference(flattening,[],[f33])).
% 7.56/1.47  
% 7.56/1.47  fof(f46,plain,(
% 7.56/1.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f34])).
% 7.56/1.47  
% 7.56/1.47  fof(f71,plain,(
% 7.56/1.47    k2_relset_1(sK1,sK2,sK3) != sK2),
% 7.56/1.47    inference(cnf_transformation,[],[f40])).
% 7.56/1.47  
% 7.56/1.47  fof(f7,axiom,(
% 7.56/1.47    k2_relat_1(k1_xboole_0) = k1_xboole_0 & k1_relat_1(k1_xboole_0) = k1_xboole_0),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f53,plain,(
% 7.56/1.47    k2_relat_1(k1_xboole_0) = k1_xboole_0),
% 7.56/1.47    inference(cnf_transformation,[],[f7])).
% 7.56/1.47  
% 7.56/1.47  fof(f8,axiom,(
% 7.56/1.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f20,plain,(
% 7.56/1.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.56/1.47    inference(ennf_transformation,[],[f8])).
% 7.56/1.47  
% 7.56/1.47  fof(f21,plain,(
% 7.56/1.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.56/1.47    inference(flattening,[],[f20])).
% 7.56/1.47  
% 7.56/1.47  fof(f35,plain,(
% 7.56/1.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.56/1.47    inference(nnf_transformation,[],[f21])).
% 7.56/1.47  
% 7.56/1.47  fof(f36,plain,(
% 7.56/1.47    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.56/1.47    inference(flattening,[],[f35])).
% 7.56/1.47  
% 7.56/1.47  fof(f56,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f36])).
% 7.56/1.47  
% 7.56/1.47  fof(f74,plain,(
% 7.56/1.47    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.56/1.47    inference(equality_resolution,[],[f56])).
% 7.56/1.47  
% 7.56/1.47  fof(f66,plain,(
% 7.56/1.47    v1_funct_1(sK3)),
% 7.56/1.47    inference(cnf_transformation,[],[f40])).
% 7.56/1.47  
% 7.56/1.47  fof(f41,plain,(
% 7.56/1.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f32])).
% 7.56/1.47  
% 7.56/1.47  fof(f4,axiom,(
% 7.56/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f17,plain,(
% 7.56/1.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.56/1.47    inference(ennf_transformation,[],[f4])).
% 7.56/1.47  
% 7.56/1.47  fof(f48,plain,(
% 7.56/1.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f17])).
% 7.56/1.47  
% 7.56/1.47  fof(f5,axiom,(
% 7.56/1.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f49,plain,(
% 7.56/1.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.56/1.47    inference(cnf_transformation,[],[f5])).
% 7.56/1.47  
% 7.56/1.47  fof(f6,axiom,(
% 7.56/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.56/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.47  
% 7.56/1.47  fof(f18,plain,(
% 7.56/1.47    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 7.56/1.47    inference(ennf_transformation,[],[f6])).
% 7.56/1.47  
% 7.56/1.47  fof(f19,plain,(
% 7.56/1.47    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 7.56/1.47    inference(flattening,[],[f18])).
% 7.56/1.47  
% 7.56/1.47  fof(f51,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f19])).
% 7.56/1.47  
% 7.56/1.47  fof(f69,plain,(
% 7.56/1.47    ( ! [X3] : (r2_hidden(sK4(X3),sK1) | ~r2_hidden(X3,sK2)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f40])).
% 7.56/1.47  
% 7.56/1.47  fof(f64,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.56/1.47    inference(cnf_transformation,[],[f37])).
% 7.56/1.47  
% 7.56/1.47  fof(f77,plain,(
% 7.56/1.47    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.56/1.47    inference(equality_resolution,[],[f64])).
% 7.56/1.47  
% 7.56/1.47  fof(f52,plain,(
% 7.56/1.47    k1_relat_1(k1_xboole_0) = k1_xboole_0),
% 7.56/1.47    inference(cnf_transformation,[],[f7])).
% 7.56/1.47  
% 7.56/1.47  fof(f50,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 7.56/1.47    inference(cnf_transformation,[],[f19])).
% 7.56/1.47  
% 7.56/1.47  fof(f61,plain,(
% 7.56/1.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.56/1.47    inference(cnf_transformation,[],[f37])).
% 7.56/1.47  
% 7.56/1.47  fof(f79,plain,(
% 7.56/1.47    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.56/1.47    inference(equality_resolution,[],[f61])).
% 7.56/1.47  
% 7.56/1.47  fof(f44,plain,(
% 7.56/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.56/1.47    inference(cnf_transformation,[],[f34])).
% 7.56/1.47  
% 7.56/1.47  fof(f73,plain,(
% 7.56/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.56/1.47    inference(equality_resolution,[],[f44])).
% 7.56/1.47  
% 7.56/1.47  cnf(c_24,plain,
% 7.56/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.47      | k1_relset_1(X1,X2,X0) = X1
% 7.56/1.47      | k1_xboole_0 = X2 ),
% 7.56/1.47      inference(cnf_transformation,[],[f60]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_29,negated_conjecture,
% 7.56/1.47      ( v1_funct_2(sK3,sK1,sK2) ),
% 7.56/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_395,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.47      | k1_relset_1(X1,X2,X0) = X1
% 7.56/1.47      | sK3 != X0
% 7.56/1.47      | sK2 != X2
% 7.56/1.47      | sK1 != X1
% 7.56/1.47      | k1_xboole_0 = X2 ),
% 7.56/1.47      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_396,plain,
% 7.56/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.56/1.47      | k1_relset_1(sK1,sK2,sK3) = sK1
% 7.56/1.47      | k1_xboole_0 = sK2 ),
% 7.56/1.47      inference(unflattening,[status(thm)],[c_395]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_28,negated_conjecture,
% 7.56/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.56/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_398,plain,
% 7.56/1.47      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_396,c_28]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_922,plain,
% 7.56/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_17,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.47      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.56/1.47      inference(cnf_transformation,[],[f58]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_926,plain,
% 7.56/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.56/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1461,plain,
% 7.56/1.47      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_922,c_926]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1536,plain,
% 7.56/1.47      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_398,c_1461]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1,plain,
% 7.56/1.47      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.56/1.47      inference(cnf_transformation,[],[f42]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_936,plain,
% 7.56/1.47      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.56/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_26,negated_conjecture,
% 7.56/1.47      ( ~ r2_hidden(X0,sK2) | k1_funct_1(sK3,sK4(X0)) = X0 ),
% 7.56/1.47      inference(cnf_transformation,[],[f70]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_924,plain,
% 7.56/1.47      ( k1_funct_1(sK3,sK4(X0)) = X0 | r2_hidden(X0,sK2) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1619,plain,
% 7.56/1.47      ( k1_funct_1(sK3,sK4(sK0(sK2,X0))) = sK0(sK2,X0)
% 7.56/1.47      | r1_tarski(sK2,X0) = iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_936,c_924]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_18,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.47      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.56/1.47      inference(cnf_transformation,[],[f59]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_925,plain,
% 7.56/1.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.56/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1404,plain,
% 7.56/1.47      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_922,c_925]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_16,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.47      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.56/1.47      inference(cnf_transformation,[],[f57]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_927,plain,
% 7.56/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.56/1.47      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1593,plain,
% 7.56/1.47      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 7.56/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_1404,c_927]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_33,plain,
% 7.56/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2015,plain,
% 7.56/1.47      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_1593,c_33]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_6,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.47      | ~ r2_hidden(X2,X0)
% 7.56/1.47      | r2_hidden(X2,X1) ),
% 7.56/1.47      inference(cnf_transformation,[],[f47]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_932,plain,
% 7.56/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.56/1.47      | r2_hidden(X2,X0) != iProver_top
% 7.56/1.47      | r2_hidden(X2,X1) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2344,plain,
% 7.56/1.47      ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r2_hidden(X0,sK2) = iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_2015,c_932]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2918,plain,
% 7.56/1.47      ( r2_hidden(sK0(k2_relat_1(sK3),X0),sK2) = iProver_top
% 7.56/1.47      | r1_tarski(k2_relat_1(sK3),X0) = iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_936,c_2344]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_0,plain,
% 7.56/1.47      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.56/1.47      inference(cnf_transformation,[],[f43]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_937,plain,
% 7.56/1.47      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.56/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3092,plain,
% 7.56/1.47      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_2918,c_937]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3,plain,
% 7.56/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.56/1.47      inference(cnf_transformation,[],[f46]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_934,plain,
% 7.56/1.47      ( X0 = X1
% 7.56/1.47      | r1_tarski(X1,X0) != iProver_top
% 7.56/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3974,plain,
% 7.56/1.47      ( k2_relat_1(sK3) = sK2
% 7.56/1.47      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_3092,c_934]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_25,negated_conjecture,
% 7.56/1.47      ( k2_relset_1(sK1,sK2,sK3) != sK2 ),
% 7.56/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1141,plain,
% 7.56/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.56/1.47      | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_18]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_560,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1125,plain,
% 7.56/1.47      ( k2_relset_1(sK1,sK2,sK3) != X0
% 7.56/1.47      | k2_relset_1(sK1,sK2,sK3) = sK2
% 7.56/1.47      | sK2 != X0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_560]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1334,plain,
% 7.56/1.47      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
% 7.56/1.47      | k2_relset_1(sK1,sK2,sK3) = sK2
% 7.56/1.47      | sK2 != k2_relat_1(sK3) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1125]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1172,plain,
% 7.56/1.47      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_3]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1521,plain,
% 7.56/1.47      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 7.56/1.47      | ~ r1_tarski(sK2,k2_relat_1(sK3))
% 7.56/1.47      | sK2 = k2_relat_1(sK3) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1172]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1522,plain,
% 7.56/1.47      ( sK2 = k2_relat_1(sK3)
% 7.56/1.47      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 7.56/1.47      | r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_1521]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3982,plain,
% 7.56/1.47      ( r1_tarski(sK2,k2_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_3974,c_28,c_25,c_1141,c_1334,c_1522,c_3092]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3987,plain,
% 7.56/1.47      ( k1_funct_1(sK3,sK4(sK0(sK2,k2_relat_1(sK3)))) = sK0(sK2,k2_relat_1(sK3)) ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_1619,c_3982]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_11,plain,
% 7.56/1.47      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_13,plain,
% 7.56/1.47      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.56/1.47      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.56/1.47      | ~ v1_funct_1(X1)
% 7.56/1.47      | ~ v1_relat_1(X1) ),
% 7.56/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_30,negated_conjecture,
% 7.56/1.47      ( v1_funct_1(sK3) ),
% 7.56/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_312,plain,
% 7.56/1.47      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.56/1.47      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.56/1.47      | ~ v1_relat_1(X1)
% 7.56/1.47      | sK3 != X1 ),
% 7.56/1.47      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_313,plain,
% 7.56/1.47      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 7.56/1.47      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
% 7.56/1.47      | ~ v1_relat_1(sK3) ),
% 7.56/1.47      inference(unflattening,[status(thm)],[c_312]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_921,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) = iProver_top
% 7.56/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2,plain,
% 7.56/1.47      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.56/1.47      inference(cnf_transformation,[],[f41]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_935,plain,
% 7.56/1.47      ( r2_hidden(X0,X1) != iProver_top
% 7.56/1.47      | r2_hidden(X0,X2) = iProver_top
% 7.56/1.47      | r1_tarski(X1,X2) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1748,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),X1) = iProver_top
% 7.56/1.47      | r1_tarski(sK3,X1) != iProver_top
% 7.56/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_921,c_935]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_7,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.47      | ~ v1_relat_1(X1)
% 7.56/1.47      | v1_relat_1(X0) ),
% 7.56/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1090,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.47      | v1_relat_1(X0)
% 7.56/1.47      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_7]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1212,plain,
% 7.56/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.56/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 7.56/1.47      | v1_relat_1(sK3) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1090]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1213,plain,
% 7.56/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.56/1.47      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 7.56/1.47      | v1_relat_1(sK3) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_1212]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_8,plain,
% 7.56/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.56/1.47      inference(cnf_transformation,[],[f49]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1232,plain,
% 7.56/1.47      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_8]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1233,plain,
% 7.56/1.47      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3386,plain,
% 7.56/1.47      ( r1_tarski(sK3,X1) != iProver_top
% 7.56/1.47      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),X1) = iProver_top
% 7.56/1.47      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_1748,c_33,c_1213,c_1233]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3387,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),X1) = iProver_top
% 7.56/1.47      | r1_tarski(sK3,X1) != iProver_top ),
% 7.56/1.47      inference(renaming,[status(thm)],[c_3386]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_9,plain,
% 7.56/1.47      ( r2_hidden(X0,k2_relat_1(X1))
% 7.56/1.47      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 7.56/1.47      | ~ v1_relat_1(X1) ),
% 7.56/1.47      inference(cnf_transformation,[],[f51]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_929,plain,
% 7.56/1.47      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 7.56/1.47      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 7.56/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3396,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(X1)) = iProver_top
% 7.56/1.47      | r1_tarski(sK3,X1) != iProver_top
% 7.56/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_3387,c_929]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_10246,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r2_hidden(k1_funct_1(sK3,X0),k1_xboole_0) = iProver_top
% 7.56/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.56/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_11,c_3396]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_10287,plain,
% 7.56/1.47      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k1_xboole_0) = iProver_top
% 7.56/1.47      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.56/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_3987,c_10246]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2372,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 7.56/1.47      | v1_relat_1(sK3) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_921,c_929]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2623,plain,
% 7.56/1.47      ( r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 7.56/1.47      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_2372,c_33,c_1213,c_1233]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2624,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 7.56/1.47      inference(renaming,[status(thm)],[c_2623]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_4202,plain,
% 7.56/1.47      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) = iProver_top
% 7.56/1.47      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),k1_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_3987,c_2624]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2877,plain,
% 7.56/1.47      ( ~ r2_hidden(sK0(X0,k2_relat_1(sK3)),k2_relat_1(sK3))
% 7.56/1.47      | r1_tarski(X0,k2_relat_1(sK3)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_4870,plain,
% 7.56/1.47      ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3))
% 7.56/1.47      | r1_tarski(sK2,k2_relat_1(sK3)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_2877]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_4871,plain,
% 7.56/1.47      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),k2_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_4870]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19538,plain,
% 7.56/1.47      ( r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),k1_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_10287,c_28,c_25,c_1141,c_1334,c_1522,c_3092,c_4202,
% 7.56/1.47                 c_4871]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19546,plain,
% 7.56/1.47      ( sK2 = k1_xboole_0
% 7.56/1.47      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_1536,c_19538]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2876,plain,
% 7.56/1.47      ( r2_hidden(sK0(X0,k2_relat_1(sK3)),X0)
% 7.56/1.47      | r1_tarski(X0,k2_relat_1(sK3)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_5114,plain,
% 7.56/1.47      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
% 7.56/1.47      | r1_tarski(sK2,k2_relat_1(sK3)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_2876]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_5115,plain,
% 7.56/1.47      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) = iProver_top
% 7.56/1.47      | r1_tarski(sK2,k2_relat_1(sK3)) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_5114]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_27,negated_conjecture,
% 7.56/1.47      ( ~ r2_hidden(X0,sK2) | r2_hidden(sK4(X0),sK1) ),
% 7.56/1.47      inference(cnf_transformation,[],[f69]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_10028,plain,
% 7.56/1.47      ( ~ r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2)
% 7.56/1.47      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_27]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_10029,plain,
% 7.56/1.47      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) != iProver_top
% 7.56/1.47      | r2_hidden(sK4(sK0(sK2,k2_relat_1(sK3))),sK1) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_10028]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19719,plain,
% 7.56/1.47      ( sK2 = k1_xboole_0 ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_19546,c_28,c_25,c_1141,c_1334,c_1522,c_3092,c_5115,
% 7.56/1.47                 c_10029]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_20,plain,
% 7.56/1.47      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.56/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.56/1.47      | k1_xboole_0 = X1
% 7.56/1.47      | k1_xboole_0 = X0 ),
% 7.56/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_362,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.56/1.47      | sK3 != X0
% 7.56/1.47      | sK2 != k1_xboole_0
% 7.56/1.47      | sK1 != X1
% 7.56/1.47      | k1_xboole_0 = X0
% 7.56/1.47      | k1_xboole_0 = X1 ),
% 7.56/1.47      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_363,plain,
% 7.56/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 7.56/1.47      | sK2 != k1_xboole_0
% 7.56/1.47      | k1_xboole_0 = sK3
% 7.56/1.47      | k1_xboole_0 = sK1 ),
% 7.56/1.47      inference(unflattening,[status(thm)],[c_362]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_919,plain,
% 7.56/1.47      ( sK2 != k1_xboole_0
% 7.56/1.47      | k1_xboole_0 = sK3
% 7.56/1.47      | k1_xboole_0 = sK1
% 7.56/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19857,plain,
% 7.56/1.47      ( sK3 = k1_xboole_0
% 7.56/1.47      | sK1 = k1_xboole_0
% 7.56/1.47      | k1_xboole_0 != k1_xboole_0
% 7.56/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.56/1.47      inference(demodulation,[status(thm)],[c_19719,c_919]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19879,plain,
% 7.56/1.47      ( sK3 = k1_xboole_0
% 7.56/1.47      | sK1 = k1_xboole_0
% 7.56/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.56/1.47      inference(equality_resolution_simp,[status(thm)],[c_19857]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19862,plain,
% 7.56/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 7.56/1.47      inference(demodulation,[status(thm)],[c_19719,c_922]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19883,plain,
% 7.56/1.47      ( sK3 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 7.56/1.47      inference(forward_subsumption_resolution,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_19879,c_19862]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_364,plain,
% 7.56/1.47      ( sK2 != k1_xboole_0
% 7.56/1.47      | k1_xboole_0 = sK3
% 7.56/1.47      | k1_xboole_0 = sK1
% 7.56/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_559,plain,( X0 = X0 ),theory(equality) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1183,plain,
% 7.56/1.47      ( sK3 = sK3 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_559]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1128,plain,
% 7.56/1.47      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_560]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1209,plain,
% 7.56/1.47      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1128]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1210,plain,
% 7.56/1.47      ( sK1 = sK1 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_559]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1176,plain,
% 7.56/1.47      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_560]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1520,plain,
% 7.56/1.47      ( k2_relat_1(sK3) != X0 | sK2 != X0 | sK2 = k2_relat_1(sK3) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1176]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1959,plain,
% 7.56/1.47      ( k2_relat_1(sK3) != k2_relat_1(X0)
% 7.56/1.47      | sK2 != k2_relat_1(X0)
% 7.56/1.47      | sK2 = k2_relat_1(sK3) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1520]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1961,plain,
% 7.56/1.47      ( k2_relat_1(sK3) != k2_relat_1(k1_xboole_0)
% 7.56/1.47      | sK2 = k2_relat_1(sK3)
% 7.56/1.47      | sK2 != k2_relat_1(k1_xboole_0) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1959]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_566,plain,
% 7.56/1.47      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 7.56/1.47      theory(equality) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1960,plain,
% 7.56/1.47      ( k2_relat_1(sK3) = k2_relat_1(X0) | sK3 != X0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_566]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1962,plain,
% 7.56/1.47      ( k2_relat_1(sK3) = k2_relat_1(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1960]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1393,plain,
% 7.56/1.47      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_560]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2243,plain,
% 7.56/1.47      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1393]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_2244,plain,
% 7.56/1.47      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_2243]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_6930,plain,
% 7.56/1.47      ( k2_relat_1(X0) != X1 | sK2 != X1 | sK2 = k2_relat_1(X0) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1176]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_6931,plain,
% 7.56/1.47      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 7.56/1.47      | sK2 = k2_relat_1(k1_xboole_0)
% 7.56/1.47      | sK2 != k1_xboole_0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_6930]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_24795,plain,
% 7.56/1.47      ( sK1 = k1_xboole_0 ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_19883,c_28,c_25,c_11,c_364,c_1141,c_1183,c_1209,
% 7.56/1.47                 c_1210,c_1334,c_1522,c_1961,c_1962,c_2244,c_3092,c_5115,
% 7.56/1.47                 c_6931,c_10029,c_19546,c_19862]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_12,plain,
% 7.56/1.47      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_923,plain,
% 7.56/1.47      ( r2_hidden(X0,sK2) != iProver_top
% 7.56/1.47      | r2_hidden(sK4(X0),sK1) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1747,plain,
% 7.56/1.47      ( r2_hidden(X0,sK2) != iProver_top
% 7.56/1.47      | r2_hidden(sK4(X0),X1) = iProver_top
% 7.56/1.47      | r1_tarski(sK1,X1) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_923,c_935]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_10,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(X1))
% 7.56/1.47      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.56/1.47      | ~ v1_relat_1(X1) ),
% 7.56/1.47      inference(cnf_transformation,[],[f50]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_928,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.56/1.47      | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top
% 7.56/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3397,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
% 7.56/1.47      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | r1_tarski(sK3,X1) != iProver_top
% 7.56/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_3387,c_928]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_8956,plain,
% 7.56/1.47      ( r2_hidden(X0,sK2) != iProver_top
% 7.56/1.47      | r2_hidden(sK4(X0),k1_relat_1(X1)) = iProver_top
% 7.56/1.47      | r1_tarski(sK3,X1) != iProver_top
% 7.56/1.47      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_1747,c_3397]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_9318,plain,
% 7.56/1.47      ( r2_hidden(X0,sK2) != iProver_top
% 7.56/1.47      | r2_hidden(sK4(X0),k1_xboole_0) = iProver_top
% 7.56/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.56/1.47      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_12,c_8956]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19775,plain,
% 7.56/1.47      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.56/1.47      | r2_hidden(sK4(X0),k1_xboole_0) = iProver_top
% 7.56/1.47      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 7.56/1.47      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
% 7.56/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.56/1.47      inference(demodulation,[status(thm)],[c_19719,c_9318]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19543,plain,
% 7.56/1.47      ( r2_hidden(sK0(sK2,k2_relat_1(sK3)),sK2) != iProver_top
% 7.56/1.47      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(superposition,[status(thm)],[c_1747,c_19538]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_21924,plain,
% 7.56/1.47      ( r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_19775,c_28,c_25,c_1141,c_1334,c_1522,c_3092,c_5115,
% 7.56/1.47                 c_19543]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_24804,plain,
% 7.56/1.47      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
% 7.56/1.47      inference(demodulation,[status(thm)],[c_24795,c_21924]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19854,plain,
% 7.56/1.47      ( k1_relset_1(sK1,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.56/1.47      inference(demodulation,[status(thm)],[c_19719,c_1461]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_24807,plain,
% 7.56/1.47      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.56/1.47      inference(demodulation,[status(thm)],[c_24795,c_19854]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_23,plain,
% 7.56/1.47      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.56/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.56/1.47      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.56/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_382,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.56/1.47      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.56/1.47      | sK3 != X0
% 7.56/1.47      | sK2 != X1
% 7.56/1.47      | sK1 != k1_xboole_0 ),
% 7.56/1.47      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_383,plain,
% 7.56/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 7.56/1.47      | k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 7.56/1.47      | sK1 != k1_xboole_0 ),
% 7.56/1.47      inference(unflattening,[status(thm)],[c_382]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_918,plain,
% 7.56/1.47      ( k1_relset_1(k1_xboole_0,sK2,sK3) = k1_xboole_0
% 7.56/1.47      | sK1 != k1_xboole_0
% 7.56/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_19858,plain,
% 7.56/1.47      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.56/1.47      | sK1 != k1_xboole_0
% 7.56/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.56/1.47      inference(demodulation,[status(thm)],[c_19719,c_918]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_5,plain,
% 7.56/1.47      ( r1_tarski(X0,X0) ),
% 7.56/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_88,plain,
% 7.56/1.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_5]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_92,plain,
% 7.56/1.47      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.56/1.47      | k1_xboole_0 = k1_xboole_0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_3]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_562,plain,
% 7.56/1.47      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.56/1.47      theory(equality) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1292,plain,
% 7.56/1.47      ( X0 != k2_zfmisc_1(sK1,sK2)
% 7.56/1.47      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_562]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1648,plain,
% 7.56/1.47      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK1,sK2)
% 7.56/1.47      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1292]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1650,plain,
% 7.56/1.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK1,sK2)
% 7.56/1.47      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1648]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_565,plain,
% 7.56/1.47      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 7.56/1.47      theory(equality) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1649,plain,
% 7.56/1.47      ( X0 != sK2
% 7.56/1.47      | X1 != sK1
% 7.56/1.47      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK1,sK2) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_565]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1651,plain,
% 7.56/1.47      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK1,sK2)
% 7.56/1.47      | k1_xboole_0 != sK2
% 7.56/1.47      | k1_xboole_0 != sK1 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1649]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1838,plain,
% 7.56/1.47      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_560]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_1839,plain,
% 7.56/1.47      ( sK2 != k1_xboole_0
% 7.56/1.47      | k1_xboole_0 = sK2
% 7.56/1.47      | k1_xboole_0 != k1_xboole_0 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_1838]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_21008,plain,
% 7.56/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 7.56/1.47      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.56/1.47      | sK1 != k1_xboole_0 ),
% 7.56/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_19858]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_563,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.56/1.47      theory(equality) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_3507,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,X1)
% 7.56/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.56/1.47      | X2 != X0
% 7.56/1.47      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_563]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_6316,plain,
% 7.56/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.56/1.47      | X2 != X0
% 7.56/1.47      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(X1) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_3507]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_17720,plain,
% 7.56/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.56/1.47      | X0 != sK3
% 7.56/1.47      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_6316]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_21509,plain,
% 7.56/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.56/1.47      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.56/1.47      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 7.56/1.47      | sK3 != sK3 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_17720]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_21511,plain,
% 7.56/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.56/1.47      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
% 7.56/1.47      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 7.56/1.47      | sK3 != sK3 ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_21509]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_22403,plain,
% 7.56/1.47      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 7.56/1.47      inference(global_propositional_subsumption,
% 7.56/1.47                [status(thm)],
% 7.56/1.47                [c_19858,c_28,c_25,c_11,c_88,c_92,c_364,c_1141,c_1183,
% 7.56/1.47                 c_1209,c_1210,c_1334,c_1522,c_1650,c_1651,c_1839,c_1961,
% 7.56/1.47                 c_1962,c_2244,c_3092,c_5115,c_6931,c_10029,c_19546,
% 7.56/1.47                 c_21008,c_19862,c_21511]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_24818,plain,
% 7.56/1.47      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.56/1.47      inference(light_normalisation,[status(thm)],[c_24807,c_22403]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_24828,plain,
% 7.56/1.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.56/1.47      inference(light_normalisation,[status(thm)],[c_24804,c_24818]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_87,plain,
% 7.56/1.47      ( r1_tarski(X0,X0) = iProver_top ),
% 7.56/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(c_89,plain,
% 7.56/1.47      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.56/1.47      inference(instantiation,[status(thm)],[c_87]) ).
% 7.56/1.47  
% 7.56/1.47  cnf(contradiction,plain,
% 7.56/1.47      ( $false ),
% 7.56/1.47      inference(minisat,[status(thm)],[c_24828,c_89]) ).
% 7.56/1.47  
% 7.56/1.47  
% 7.56/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.56/1.47  
% 7.56/1.47  ------                               Statistics
% 7.56/1.47  
% 7.56/1.47  ------ General
% 7.56/1.47  
% 7.56/1.47  abstr_ref_over_cycles:                  0
% 7.56/1.47  abstr_ref_under_cycles:                 0
% 7.56/1.47  gc_basic_clause_elim:                   0
% 7.56/1.47  forced_gc_time:                         0
% 7.56/1.47  parsing_time:                           0.013
% 7.56/1.47  unif_index_cands_time:                  0.
% 7.56/1.47  unif_index_add_time:                    0.
% 7.56/1.47  orderings_time:                         0.
% 7.56/1.47  out_proof_time:                         0.013
% 7.56/1.47  total_time:                             0.838
% 7.56/1.47  num_of_symbols:                         51
% 7.56/1.47  num_of_terms:                           15373
% 7.56/1.47  
% 7.56/1.47  ------ Preprocessing
% 7.56/1.47  
% 7.56/1.47  num_of_splits:                          0
% 7.56/1.47  num_of_split_atoms:                     0
% 7.56/1.47  num_of_reused_defs:                     0
% 7.56/1.47  num_eq_ax_congr_red:                    20
% 7.56/1.47  num_of_sem_filtered_clauses:            1
% 7.56/1.47  num_of_subtypes:                        0
% 7.56/1.47  monotx_restored_types:                  0
% 7.56/1.47  sat_num_of_epr_types:                   0
% 7.56/1.47  sat_num_of_non_cyclic_types:            0
% 7.56/1.47  sat_guarded_non_collapsed_types:        0
% 7.56/1.47  num_pure_diseq_elim:                    0
% 7.56/1.47  simp_replaced_by:                       0
% 7.56/1.47  res_preprocessed:                       128
% 7.56/1.47  prep_upred:                             0
% 7.56/1.47  prep_unflattend:                        29
% 7.56/1.47  smt_new_axioms:                         0
% 7.56/1.47  pred_elim_cands:                        4
% 7.56/1.47  pred_elim:                              2
% 7.56/1.47  pred_elim_cl:                           5
% 7.56/1.47  pred_elim_cycles:                       4
% 7.56/1.47  merged_defs:                            0
% 7.56/1.47  merged_defs_ncl:                        0
% 7.56/1.47  bin_hyper_res:                          0
% 7.56/1.47  prep_cycles:                            4
% 7.56/1.47  pred_elim_time:                         0.005
% 7.56/1.47  splitting_time:                         0.
% 7.56/1.47  sem_filter_time:                        0.
% 7.56/1.47  monotx_time:                            0.001
% 7.56/1.47  subtype_inf_time:                       0.
% 7.56/1.47  
% 7.56/1.47  ------ Problem properties
% 7.56/1.47  
% 7.56/1.47  clauses:                                24
% 7.56/1.47  conjectures:                            4
% 7.56/1.47  epr:                                    3
% 7.56/1.47  horn:                                   21
% 7.56/1.47  ground:                                 7
% 7.56/1.47  unary:                                  6
% 7.56/1.47  binary:                                 8
% 7.56/1.47  lits:                                   53
% 7.56/1.47  lits_eq:                                15
% 7.56/1.47  fd_pure:                                0
% 7.56/1.47  fd_pseudo:                              0
% 7.56/1.47  fd_cond:                                0
% 7.56/1.47  fd_pseudo_cond:                         2
% 7.56/1.47  ac_symbols:                             0
% 7.56/1.47  
% 7.56/1.47  ------ Propositional Solver
% 7.56/1.47  
% 7.56/1.47  prop_solver_calls:                      32
% 7.56/1.47  prop_fast_solver_calls:                 1314
% 7.56/1.47  smt_solver_calls:                       0
% 7.56/1.47  smt_fast_solver_calls:                  0
% 7.56/1.47  prop_num_of_clauses:                    8389
% 7.56/1.47  prop_preprocess_simplified:             11369
% 7.56/1.47  prop_fo_subsumed:                       28
% 7.56/1.47  prop_solver_time:                       0.
% 7.56/1.47  smt_solver_time:                        0.
% 7.56/1.47  smt_fast_solver_time:                   0.
% 7.56/1.47  prop_fast_solver_time:                  0.
% 7.56/1.47  prop_unsat_core_time:                   0.
% 7.56/1.47  
% 7.56/1.47  ------ QBF
% 7.56/1.47  
% 7.56/1.47  qbf_q_res:                              0
% 7.56/1.47  qbf_num_tautologies:                    0
% 7.56/1.47  qbf_prep_cycles:                        0
% 7.56/1.47  
% 7.56/1.47  ------ BMC1
% 7.56/1.47  
% 7.56/1.47  bmc1_current_bound:                     -1
% 7.56/1.47  bmc1_last_solved_bound:                 -1
% 7.56/1.47  bmc1_unsat_core_size:                   -1
% 7.56/1.47  bmc1_unsat_core_parents_size:           -1
% 7.56/1.47  bmc1_merge_next_fun:                    0
% 7.56/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.56/1.47  
% 7.56/1.47  ------ Instantiation
% 7.56/1.47  
% 7.56/1.47  inst_num_of_clauses:                    1761
% 7.56/1.47  inst_num_in_passive:                    516
% 7.56/1.47  inst_num_in_active:                     797
% 7.56/1.47  inst_num_in_unprocessed:                448
% 7.56/1.47  inst_num_of_loops:                      1080
% 7.56/1.47  inst_num_of_learning_restarts:          0
% 7.56/1.47  inst_num_moves_active_passive:          277
% 7.56/1.47  inst_lit_activity:                      0
% 7.56/1.47  inst_lit_activity_moves:                0
% 7.56/1.47  inst_num_tautologies:                   0
% 7.56/1.47  inst_num_prop_implied:                  0
% 7.56/1.47  inst_num_existing_simplified:           0
% 7.56/1.47  inst_num_eq_res_simplified:             0
% 7.56/1.47  inst_num_child_elim:                    0
% 7.56/1.47  inst_num_of_dismatching_blockings:      1261
% 7.56/1.47  inst_num_of_non_proper_insts:           2270
% 7.56/1.47  inst_num_of_duplicates:                 0
% 7.56/1.47  inst_inst_num_from_inst_to_res:         0
% 7.56/1.47  inst_dismatching_checking_time:         0.
% 7.56/1.47  
% 7.56/1.47  ------ Resolution
% 7.56/1.47  
% 7.56/1.47  res_num_of_clauses:                     0
% 7.56/1.47  res_num_in_passive:                     0
% 7.56/1.47  res_num_in_active:                      0
% 7.56/1.47  res_num_of_loops:                       132
% 7.56/1.47  res_forward_subset_subsumed:            163
% 7.56/1.47  res_backward_subset_subsumed:           2
% 7.56/1.47  res_forward_subsumed:                   0
% 7.56/1.47  res_backward_subsumed:                  0
% 7.56/1.47  res_forward_subsumption_resolution:     0
% 7.56/1.47  res_backward_subsumption_resolution:    0
% 7.56/1.47  res_clause_to_clause_subsumption:       19030
% 7.56/1.47  res_orphan_elimination:                 0
% 7.56/1.47  res_tautology_del:                      306
% 7.56/1.47  res_num_eq_res_simplified:              0
% 7.56/1.47  res_num_sel_changes:                    0
% 7.56/1.47  res_moves_from_active_to_pass:          0
% 7.56/1.47  
% 7.56/1.47  ------ Superposition
% 7.56/1.47  
% 7.56/1.47  sup_time_total:                         0.
% 7.56/1.47  sup_time_generating:                    0.
% 7.56/1.47  sup_time_sim_full:                      0.
% 7.56/1.47  sup_time_sim_immed:                     0.
% 7.56/1.47  
% 7.56/1.47  sup_num_of_clauses:                     818
% 7.56/1.47  sup_num_in_active:                      56
% 7.56/1.47  sup_num_in_passive:                     762
% 7.56/1.47  sup_num_of_loops:                       214
% 7.56/1.47  sup_fw_superposition:                   765
% 7.56/1.47  sup_bw_superposition:                   393
% 7.56/1.47  sup_immediate_simplified:               240
% 7.56/1.47  sup_given_eliminated:                   0
% 7.56/1.47  comparisons_done:                       0
% 7.56/1.47  comparisons_avoided:                    11
% 7.56/1.47  
% 7.56/1.47  ------ Simplifications
% 7.56/1.47  
% 7.56/1.47  
% 7.56/1.47  sim_fw_subset_subsumed:                 78
% 7.56/1.47  sim_bw_subset_subsumed:                 18
% 7.56/1.47  sim_fw_subsumed:                        52
% 7.56/1.47  sim_bw_subsumed:                        104
% 7.56/1.47  sim_fw_subsumption_res:                 1
% 7.56/1.47  sim_bw_subsumption_res:                 0
% 7.56/1.47  sim_tautology_del:                      3
% 7.56/1.47  sim_eq_tautology_del:                   36
% 7.56/1.47  sim_eq_res_simp:                        1
% 7.56/1.47  sim_fw_demodulated:                     0
% 7.56/1.47  sim_bw_demodulated:                     155
% 7.56/1.47  sim_light_normalised:                   11
% 7.56/1.47  sim_joinable_taut:                      0
% 7.56/1.47  sim_joinable_simp:                      0
% 7.56/1.47  sim_ac_normalised:                      0
% 7.56/1.47  sim_smt_subsumption:                    0
% 7.56/1.47  
%------------------------------------------------------------------------------
