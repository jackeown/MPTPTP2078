%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:14 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 616 expanded)
%              Number of clauses        :   96 ( 242 expanded)
%              Number of leaves         :   18 ( 115 expanded)
%              Depth                    :   20
%              Number of atoms          :  454 (2434 expanded)
%              Number of equality atoms :  212 ( 609 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
        | ~ v1_funct_1(sK2) )
      & r1_tarski(k2_relat_1(sK2),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
      | ~ v1_funct_1(sK2) )
    & r1_tarski(k2_relat_1(sK2),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f38])).

fof(f69,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f16])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1049,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1769,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1049])).

cnf(c_23,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_141,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_28])).

cnf(c_142,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK2) != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_142])).

cnf(c_419,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_xboole_0 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_419,c_18])).

cnf(c_1043,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_2397,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_1043])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_15,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_343,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_344,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_610,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1269,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_1363,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_609,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1364,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1217,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1443,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK2,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_1544,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_1245,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1481,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK2))))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_2340,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_2616,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2397,c_27,c_344,c_427,c_1363,c_1364,c_1544,c_2340])).

cnf(c_1048,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2623,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2616,c_1048])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1054,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1052,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1473,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1052])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1056,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1866,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_1056])).

cnf(c_2656,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2623,c_1866])).

cnf(c_1047,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_2775,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2656,c_1047])).

cnf(c_2777,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2775,c_7])).

cnf(c_2800,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2777,c_1866])).

cnf(c_2346,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2340])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_199,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_200,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_199])).

cnf(c_254,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_200])).

cnf(c_352,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_254])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_2290,plain,
    ( ~ r2_hidden(sK0(sK2,k2_zfmisc_1(X0,X1)),sK2)
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_2291,plain,
    ( r2_hidden(sK0(sK2,k2_zfmisc_1(X0,X1)),sK2) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2290])).

cnf(c_2293,plain,
    ( r2_hidden(sK0(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2291])).

cnf(c_2188,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2189,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2188])).

cnf(c_1807,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) != X0
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_2187,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relat_1(sK2)
    | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_1545,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1523,plain,
    ( r2_hidden(sK0(sK2,k2_zfmisc_1(X0,X1)),sK2)
    | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1534,plain,
    ( r2_hidden(sK0(sK2,k2_zfmisc_1(X0,X1)),sK2) = iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_1536,plain,
    ( r2_hidden(sK0(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2) = iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_1444,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1443])).

cnf(c_1446,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_1372,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_1373,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_616,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1293,plain,
    ( k1_relat_1(sK2) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_1295,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_1270,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_1292,plain,
    ( k1_relat_1(sK2) != k1_relat_1(X0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_1294,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1292])).

cnf(c_1246,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_1248,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_142])).

cnf(c_403,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_404,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_20,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_375,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_relat_1(sK2) != X0
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_142])).

cnf(c_376,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_376,c_10])).

cnf(c_345,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_75,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_32,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2800,c_2777,c_2346,c_2340,c_2293,c_2189,c_2187,c_1545,c_1544,c_1536,c_1446,c_1373,c_1364,c_1363,c_1295,c_1294,c_1248,c_427,c_404,c_388,c_345,c_344,c_75,c_74,c_17,c_32,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:50:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.33/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.98  
% 2.33/0.98  ------  iProver source info
% 2.33/0.98  
% 2.33/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.98  git: non_committed_changes: false
% 2.33/0.98  git: last_make_outside_of_git: false
% 2.33/0.98  
% 2.33/0.98  ------ 
% 2.33/0.98  
% 2.33/0.98  ------ Input Options
% 2.33/0.98  
% 2.33/0.98  --out_options                           all
% 2.33/0.98  --tptp_safe_out                         true
% 2.33/0.98  --problem_path                          ""
% 2.33/0.98  --include_path                          ""
% 2.33/0.98  --clausifier                            res/vclausify_rel
% 2.33/0.98  --clausifier_options                    --mode clausify
% 2.33/0.98  --stdin                                 false
% 2.33/0.98  --stats_out                             all
% 2.33/0.98  
% 2.33/0.98  ------ General Options
% 2.33/0.98  
% 2.33/0.98  --fof                                   false
% 2.33/0.98  --time_out_real                         305.
% 2.33/0.98  --time_out_virtual                      -1.
% 2.33/0.98  --symbol_type_check                     false
% 2.33/0.98  --clausify_out                          false
% 2.33/0.98  --sig_cnt_out                           false
% 2.33/0.98  --trig_cnt_out                          false
% 2.33/0.98  --trig_cnt_out_tolerance                1.
% 2.33/0.98  --trig_cnt_out_sk_spl                   false
% 2.33/0.98  --abstr_cl_out                          false
% 2.33/0.98  
% 2.33/0.98  ------ Global Options
% 2.33/0.98  
% 2.33/0.98  --schedule                              default
% 2.33/0.98  --add_important_lit                     false
% 2.33/0.98  --prop_solver_per_cl                    1000
% 2.33/0.98  --min_unsat_core                        false
% 2.33/0.98  --soft_assumptions                      false
% 2.33/0.98  --soft_lemma_size                       3
% 2.33/0.98  --prop_impl_unit_size                   0
% 2.33/0.98  --prop_impl_unit                        []
% 2.33/0.98  --share_sel_clauses                     true
% 2.33/0.98  --reset_solvers                         false
% 2.33/0.98  --bc_imp_inh                            [conj_cone]
% 2.33/0.98  --conj_cone_tolerance                   3.
% 2.33/0.98  --extra_neg_conj                        none
% 2.33/0.98  --large_theory_mode                     true
% 2.33/0.98  --prolific_symb_bound                   200
% 2.33/0.98  --lt_threshold                          2000
% 2.33/0.98  --clause_weak_htbl                      true
% 2.33/0.98  --gc_record_bc_elim                     false
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing Options
% 2.33/0.98  
% 2.33/0.98  --preprocessing_flag                    true
% 2.33/0.98  --time_out_prep_mult                    0.1
% 2.33/0.98  --splitting_mode                        input
% 2.33/0.98  --splitting_grd                         true
% 2.33/0.98  --splitting_cvd                         false
% 2.33/0.98  --splitting_cvd_svl                     false
% 2.33/0.98  --splitting_nvd                         32
% 2.33/0.98  --sub_typing                            true
% 2.33/0.98  --prep_gs_sim                           true
% 2.33/0.98  --prep_unflatten                        true
% 2.33/0.98  --prep_res_sim                          true
% 2.33/0.98  --prep_upred                            true
% 2.33/0.98  --prep_sem_filter                       exhaustive
% 2.33/0.98  --prep_sem_filter_out                   false
% 2.33/0.98  --pred_elim                             true
% 2.33/0.98  --res_sim_input                         true
% 2.33/0.98  --eq_ax_congr_red                       true
% 2.33/0.98  --pure_diseq_elim                       true
% 2.33/0.98  --brand_transform                       false
% 2.33/0.98  --non_eq_to_eq                          false
% 2.33/0.98  --prep_def_merge                        true
% 2.33/0.98  --prep_def_merge_prop_impl              false
% 2.33/0.98  --prep_def_merge_mbd                    true
% 2.33/0.98  --prep_def_merge_tr_red                 false
% 2.33/0.98  --prep_def_merge_tr_cl                  false
% 2.33/0.98  --smt_preprocessing                     true
% 2.33/0.98  --smt_ac_axioms                         fast
% 2.33/0.98  --preprocessed_out                      false
% 2.33/0.98  --preprocessed_stats                    false
% 2.33/0.98  
% 2.33/0.98  ------ Abstraction refinement Options
% 2.33/0.98  
% 2.33/0.98  --abstr_ref                             []
% 2.33/0.98  --abstr_ref_prep                        false
% 2.33/0.98  --abstr_ref_until_sat                   false
% 2.33/0.98  --abstr_ref_sig_restrict                funpre
% 2.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.98  --abstr_ref_under                       []
% 2.33/0.98  
% 2.33/0.98  ------ SAT Options
% 2.33/0.98  
% 2.33/0.98  --sat_mode                              false
% 2.33/0.98  --sat_fm_restart_options                ""
% 2.33/0.98  --sat_gr_def                            false
% 2.33/0.98  --sat_epr_types                         true
% 2.33/0.98  --sat_non_cyclic_types                  false
% 2.33/0.98  --sat_finite_models                     false
% 2.33/0.98  --sat_fm_lemmas                         false
% 2.33/0.98  --sat_fm_prep                           false
% 2.33/0.98  --sat_fm_uc_incr                        true
% 2.33/0.98  --sat_out_model                         small
% 2.33/0.98  --sat_out_clauses                       false
% 2.33/0.98  
% 2.33/0.98  ------ QBF Options
% 2.33/0.98  
% 2.33/0.98  --qbf_mode                              false
% 2.33/0.98  --qbf_elim_univ                         false
% 2.33/0.98  --qbf_dom_inst                          none
% 2.33/0.98  --qbf_dom_pre_inst                      false
% 2.33/0.98  --qbf_sk_in                             false
% 2.33/0.98  --qbf_pred_elim                         true
% 2.33/0.98  --qbf_split                             512
% 2.33/0.98  
% 2.33/0.98  ------ BMC1 Options
% 2.33/0.98  
% 2.33/0.98  --bmc1_incremental                      false
% 2.33/0.98  --bmc1_axioms                           reachable_all
% 2.33/0.98  --bmc1_min_bound                        0
% 2.33/0.98  --bmc1_max_bound                        -1
% 2.33/0.98  --bmc1_max_bound_default                -1
% 2.33/0.98  --bmc1_symbol_reachability              true
% 2.33/0.98  --bmc1_property_lemmas                  false
% 2.33/0.98  --bmc1_k_induction                      false
% 2.33/0.98  --bmc1_non_equiv_states                 false
% 2.33/0.98  --bmc1_deadlock                         false
% 2.33/0.98  --bmc1_ucm                              false
% 2.33/0.98  --bmc1_add_unsat_core                   none
% 2.33/0.98  --bmc1_unsat_core_children              false
% 2.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.98  --bmc1_out_stat                         full
% 2.33/0.98  --bmc1_ground_init                      false
% 2.33/0.98  --bmc1_pre_inst_next_state              false
% 2.33/0.98  --bmc1_pre_inst_state                   false
% 2.33/0.98  --bmc1_pre_inst_reach_state             false
% 2.33/0.98  --bmc1_out_unsat_core                   false
% 2.33/0.98  --bmc1_aig_witness_out                  false
% 2.33/0.98  --bmc1_verbose                          false
% 2.33/0.98  --bmc1_dump_clauses_tptp                false
% 2.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.98  --bmc1_dump_file                        -
% 2.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.98  --bmc1_ucm_extend_mode                  1
% 2.33/0.98  --bmc1_ucm_init_mode                    2
% 2.33/0.98  --bmc1_ucm_cone_mode                    none
% 2.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.98  --bmc1_ucm_relax_model                  4
% 2.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.98  --bmc1_ucm_layered_model                none
% 2.33/0.98  --bmc1_ucm_max_lemma_size               10
% 2.33/0.98  
% 2.33/0.98  ------ AIG Options
% 2.33/0.98  
% 2.33/0.98  --aig_mode                              false
% 2.33/0.98  
% 2.33/0.98  ------ Instantiation Options
% 2.33/0.98  
% 2.33/0.98  --instantiation_flag                    true
% 2.33/0.98  --inst_sos_flag                         false
% 2.33/0.98  --inst_sos_phase                        true
% 2.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel_side                     num_symb
% 2.33/0.98  --inst_solver_per_active                1400
% 2.33/0.98  --inst_solver_calls_frac                1.
% 2.33/0.98  --inst_passive_queue_type               priority_queues
% 2.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.98  --inst_passive_queues_freq              [25;2]
% 2.33/0.98  --inst_dismatching                      true
% 2.33/0.98  --inst_eager_unprocessed_to_passive     true
% 2.33/0.98  --inst_prop_sim_given                   true
% 2.33/0.98  --inst_prop_sim_new                     false
% 2.33/0.98  --inst_subs_new                         false
% 2.33/0.98  --inst_eq_res_simp                      false
% 2.33/0.98  --inst_subs_given                       false
% 2.33/0.98  --inst_orphan_elimination               true
% 2.33/0.98  --inst_learning_loop_flag               true
% 2.33/0.98  --inst_learning_start                   3000
% 2.33/0.98  --inst_learning_factor                  2
% 2.33/0.98  --inst_start_prop_sim_after_learn       3
% 2.33/0.98  --inst_sel_renew                        solver
% 2.33/0.98  --inst_lit_activity_flag                true
% 2.33/0.98  --inst_restr_to_given                   false
% 2.33/0.98  --inst_activity_threshold               500
% 2.33/0.98  --inst_out_proof                        true
% 2.33/0.98  
% 2.33/0.98  ------ Resolution Options
% 2.33/0.98  
% 2.33/0.98  --resolution_flag                       true
% 2.33/0.98  --res_lit_sel                           adaptive
% 2.33/0.98  --res_lit_sel_side                      none
% 2.33/0.98  --res_ordering                          kbo
% 2.33/0.98  --res_to_prop_solver                    active
% 2.33/0.98  --res_prop_simpl_new                    false
% 2.33/0.98  --res_prop_simpl_given                  true
% 2.33/0.98  --res_passive_queue_type                priority_queues
% 2.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.98  --res_passive_queues_freq               [15;5]
% 2.33/0.98  --res_forward_subs                      full
% 2.33/0.98  --res_backward_subs                     full
% 2.33/0.98  --res_forward_subs_resolution           true
% 2.33/0.98  --res_backward_subs_resolution          true
% 2.33/0.98  --res_orphan_elimination                true
% 2.33/0.98  --res_time_limit                        2.
% 2.33/0.98  --res_out_proof                         true
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Options
% 2.33/0.98  
% 2.33/0.98  --superposition_flag                    true
% 2.33/0.98  --sup_passive_queue_type                priority_queues
% 2.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.98  --demod_completeness_check              fast
% 2.33/0.98  --demod_use_ground                      true
% 2.33/0.98  --sup_to_prop_solver                    passive
% 2.33/0.98  --sup_prop_simpl_new                    true
% 2.33/0.98  --sup_prop_simpl_given                  true
% 2.33/0.98  --sup_fun_splitting                     false
% 2.33/0.98  --sup_smt_interval                      50000
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Simplification Setup
% 2.33/0.98  
% 2.33/0.98  --sup_indices_passive                   []
% 2.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_full_bw                           [BwDemod]
% 2.33/0.98  --sup_immed_triv                        [TrivRules]
% 2.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_immed_bw_main                     []
% 2.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  
% 2.33/0.98  ------ Combination Options
% 2.33/0.98  
% 2.33/0.98  --comb_res_mult                         3
% 2.33/0.98  --comb_sup_mult                         2
% 2.33/0.98  --comb_inst_mult                        10
% 2.33/0.98  
% 2.33/0.98  ------ Debug Options
% 2.33/0.98  
% 2.33/0.98  --dbg_backtrace                         false
% 2.33/0.98  --dbg_dump_prop_clauses                 false
% 2.33/0.98  --dbg_dump_prop_clauses_file            -
% 2.33/0.98  --dbg_out_stat                          false
% 2.33/0.98  ------ Parsing...
% 2.33/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.98  ------ Proving...
% 2.33/0.98  ------ Problem Properties 
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  clauses                                 22
% 2.33/0.98  conjectures                             1
% 2.33/0.98  EPR                                     4
% 2.33/0.98  Horn                                    20
% 2.33/0.98  unary                                   8
% 2.33/0.98  binary                                  7
% 2.33/0.98  lits                                    45
% 2.33/0.98  lits eq                                 15
% 2.33/0.98  fd_pure                                 0
% 2.33/0.98  fd_pseudo                               0
% 2.33/0.98  fd_cond                                 1
% 2.33/0.98  fd_pseudo_cond                          1
% 2.33/0.98  AC symbols                              0
% 2.33/0.98  
% 2.33/0.98  ------ Schedule dynamic 5 is on 
% 2.33/0.98  
% 2.33/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  ------ 
% 2.33/0.98  Current options:
% 2.33/0.98  ------ 
% 2.33/0.98  
% 2.33/0.98  ------ Input Options
% 2.33/0.98  
% 2.33/0.98  --out_options                           all
% 2.33/0.98  --tptp_safe_out                         true
% 2.33/0.98  --problem_path                          ""
% 2.33/0.98  --include_path                          ""
% 2.33/0.98  --clausifier                            res/vclausify_rel
% 2.33/0.98  --clausifier_options                    --mode clausify
% 2.33/0.98  --stdin                                 false
% 2.33/0.98  --stats_out                             all
% 2.33/0.98  
% 2.33/0.98  ------ General Options
% 2.33/0.98  
% 2.33/0.98  --fof                                   false
% 2.33/0.98  --time_out_real                         305.
% 2.33/0.98  --time_out_virtual                      -1.
% 2.33/0.98  --symbol_type_check                     false
% 2.33/0.98  --clausify_out                          false
% 2.33/0.98  --sig_cnt_out                           false
% 2.33/0.98  --trig_cnt_out                          false
% 2.33/0.98  --trig_cnt_out_tolerance                1.
% 2.33/0.98  --trig_cnt_out_sk_spl                   false
% 2.33/0.98  --abstr_cl_out                          false
% 2.33/0.98  
% 2.33/0.98  ------ Global Options
% 2.33/0.98  
% 2.33/0.98  --schedule                              default
% 2.33/0.98  --add_important_lit                     false
% 2.33/0.98  --prop_solver_per_cl                    1000
% 2.33/0.98  --min_unsat_core                        false
% 2.33/0.98  --soft_assumptions                      false
% 2.33/0.98  --soft_lemma_size                       3
% 2.33/0.98  --prop_impl_unit_size                   0
% 2.33/0.98  --prop_impl_unit                        []
% 2.33/0.98  --share_sel_clauses                     true
% 2.33/0.98  --reset_solvers                         false
% 2.33/0.98  --bc_imp_inh                            [conj_cone]
% 2.33/0.98  --conj_cone_tolerance                   3.
% 2.33/0.98  --extra_neg_conj                        none
% 2.33/0.98  --large_theory_mode                     true
% 2.33/0.98  --prolific_symb_bound                   200
% 2.33/0.98  --lt_threshold                          2000
% 2.33/0.98  --clause_weak_htbl                      true
% 2.33/0.98  --gc_record_bc_elim                     false
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing Options
% 2.33/0.98  
% 2.33/0.98  --preprocessing_flag                    true
% 2.33/0.98  --time_out_prep_mult                    0.1
% 2.33/0.98  --splitting_mode                        input
% 2.33/0.98  --splitting_grd                         true
% 2.33/0.98  --splitting_cvd                         false
% 2.33/0.98  --splitting_cvd_svl                     false
% 2.33/0.98  --splitting_nvd                         32
% 2.33/0.98  --sub_typing                            true
% 2.33/0.98  --prep_gs_sim                           true
% 2.33/0.98  --prep_unflatten                        true
% 2.33/0.98  --prep_res_sim                          true
% 2.33/0.98  --prep_upred                            true
% 2.33/0.98  --prep_sem_filter                       exhaustive
% 2.33/0.98  --prep_sem_filter_out                   false
% 2.33/0.98  --pred_elim                             true
% 2.33/0.98  --res_sim_input                         true
% 2.33/0.98  --eq_ax_congr_red                       true
% 2.33/0.98  --pure_diseq_elim                       true
% 2.33/0.98  --brand_transform                       false
% 2.33/0.98  --non_eq_to_eq                          false
% 2.33/0.98  --prep_def_merge                        true
% 2.33/0.98  --prep_def_merge_prop_impl              false
% 2.33/0.98  --prep_def_merge_mbd                    true
% 2.33/0.98  --prep_def_merge_tr_red                 false
% 2.33/0.98  --prep_def_merge_tr_cl                  false
% 2.33/0.98  --smt_preprocessing                     true
% 2.33/0.98  --smt_ac_axioms                         fast
% 2.33/0.98  --preprocessed_out                      false
% 2.33/0.98  --preprocessed_stats                    false
% 2.33/0.98  
% 2.33/0.98  ------ Abstraction refinement Options
% 2.33/0.98  
% 2.33/0.98  --abstr_ref                             []
% 2.33/0.98  --abstr_ref_prep                        false
% 2.33/0.98  --abstr_ref_until_sat                   false
% 2.33/0.98  --abstr_ref_sig_restrict                funpre
% 2.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.98  --abstr_ref_under                       []
% 2.33/0.98  
% 2.33/0.98  ------ SAT Options
% 2.33/0.98  
% 2.33/0.98  --sat_mode                              false
% 2.33/0.98  --sat_fm_restart_options                ""
% 2.33/0.98  --sat_gr_def                            false
% 2.33/0.98  --sat_epr_types                         true
% 2.33/0.98  --sat_non_cyclic_types                  false
% 2.33/0.98  --sat_finite_models                     false
% 2.33/0.98  --sat_fm_lemmas                         false
% 2.33/0.98  --sat_fm_prep                           false
% 2.33/0.98  --sat_fm_uc_incr                        true
% 2.33/0.98  --sat_out_model                         small
% 2.33/0.98  --sat_out_clauses                       false
% 2.33/0.98  
% 2.33/0.98  ------ QBF Options
% 2.33/0.98  
% 2.33/0.98  --qbf_mode                              false
% 2.33/0.98  --qbf_elim_univ                         false
% 2.33/0.98  --qbf_dom_inst                          none
% 2.33/0.98  --qbf_dom_pre_inst                      false
% 2.33/0.98  --qbf_sk_in                             false
% 2.33/0.98  --qbf_pred_elim                         true
% 2.33/0.98  --qbf_split                             512
% 2.33/0.98  
% 2.33/0.98  ------ BMC1 Options
% 2.33/0.98  
% 2.33/0.98  --bmc1_incremental                      false
% 2.33/0.98  --bmc1_axioms                           reachable_all
% 2.33/0.98  --bmc1_min_bound                        0
% 2.33/0.98  --bmc1_max_bound                        -1
% 2.33/0.98  --bmc1_max_bound_default                -1
% 2.33/0.98  --bmc1_symbol_reachability              true
% 2.33/0.98  --bmc1_property_lemmas                  false
% 2.33/0.98  --bmc1_k_induction                      false
% 2.33/0.98  --bmc1_non_equiv_states                 false
% 2.33/0.98  --bmc1_deadlock                         false
% 2.33/0.98  --bmc1_ucm                              false
% 2.33/0.98  --bmc1_add_unsat_core                   none
% 2.33/0.98  --bmc1_unsat_core_children              false
% 2.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.98  --bmc1_out_stat                         full
% 2.33/0.98  --bmc1_ground_init                      false
% 2.33/0.98  --bmc1_pre_inst_next_state              false
% 2.33/0.98  --bmc1_pre_inst_state                   false
% 2.33/0.98  --bmc1_pre_inst_reach_state             false
% 2.33/0.98  --bmc1_out_unsat_core                   false
% 2.33/0.98  --bmc1_aig_witness_out                  false
% 2.33/0.98  --bmc1_verbose                          false
% 2.33/0.98  --bmc1_dump_clauses_tptp                false
% 2.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.98  --bmc1_dump_file                        -
% 2.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.98  --bmc1_ucm_extend_mode                  1
% 2.33/0.98  --bmc1_ucm_init_mode                    2
% 2.33/0.98  --bmc1_ucm_cone_mode                    none
% 2.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.98  --bmc1_ucm_relax_model                  4
% 2.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.98  --bmc1_ucm_layered_model                none
% 2.33/0.98  --bmc1_ucm_max_lemma_size               10
% 2.33/0.98  
% 2.33/0.98  ------ AIG Options
% 2.33/0.98  
% 2.33/0.98  --aig_mode                              false
% 2.33/0.98  
% 2.33/0.98  ------ Instantiation Options
% 2.33/0.98  
% 2.33/0.98  --instantiation_flag                    true
% 2.33/0.98  --inst_sos_flag                         false
% 2.33/0.98  --inst_sos_phase                        true
% 2.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.98  --inst_lit_sel_side                     none
% 2.33/0.98  --inst_solver_per_active                1400
% 2.33/0.98  --inst_solver_calls_frac                1.
% 2.33/0.98  --inst_passive_queue_type               priority_queues
% 2.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.98  --inst_passive_queues_freq              [25;2]
% 2.33/0.98  --inst_dismatching                      true
% 2.33/0.98  --inst_eager_unprocessed_to_passive     true
% 2.33/0.98  --inst_prop_sim_given                   true
% 2.33/0.98  --inst_prop_sim_new                     false
% 2.33/0.98  --inst_subs_new                         false
% 2.33/0.98  --inst_eq_res_simp                      false
% 2.33/0.98  --inst_subs_given                       false
% 2.33/0.98  --inst_orphan_elimination               true
% 2.33/0.98  --inst_learning_loop_flag               true
% 2.33/0.98  --inst_learning_start                   3000
% 2.33/0.98  --inst_learning_factor                  2
% 2.33/0.98  --inst_start_prop_sim_after_learn       3
% 2.33/0.98  --inst_sel_renew                        solver
% 2.33/0.98  --inst_lit_activity_flag                true
% 2.33/0.98  --inst_restr_to_given                   false
% 2.33/0.98  --inst_activity_threshold               500
% 2.33/0.98  --inst_out_proof                        true
% 2.33/0.98  
% 2.33/0.98  ------ Resolution Options
% 2.33/0.98  
% 2.33/0.98  --resolution_flag                       false
% 2.33/0.98  --res_lit_sel                           adaptive
% 2.33/0.98  --res_lit_sel_side                      none
% 2.33/0.98  --res_ordering                          kbo
% 2.33/0.98  --res_to_prop_solver                    active
% 2.33/0.98  --res_prop_simpl_new                    false
% 2.33/0.98  --res_prop_simpl_given                  true
% 2.33/0.98  --res_passive_queue_type                priority_queues
% 2.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.98  --res_passive_queues_freq               [15;5]
% 2.33/0.98  --res_forward_subs                      full
% 2.33/0.98  --res_backward_subs                     full
% 2.33/0.98  --res_forward_subs_resolution           true
% 2.33/0.98  --res_backward_subs_resolution          true
% 2.33/0.98  --res_orphan_elimination                true
% 2.33/0.98  --res_time_limit                        2.
% 2.33/0.98  --res_out_proof                         true
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Options
% 2.33/0.98  
% 2.33/0.98  --superposition_flag                    true
% 2.33/0.98  --sup_passive_queue_type                priority_queues
% 2.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.98  --demod_completeness_check              fast
% 2.33/0.98  --demod_use_ground                      true
% 2.33/0.98  --sup_to_prop_solver                    passive
% 2.33/0.98  --sup_prop_simpl_new                    true
% 2.33/0.98  --sup_prop_simpl_given                  true
% 2.33/0.98  --sup_fun_splitting                     false
% 2.33/0.98  --sup_smt_interval                      50000
% 2.33/0.98  
% 2.33/0.98  ------ Superposition Simplification Setup
% 2.33/0.98  
% 2.33/0.98  --sup_indices_passive                   []
% 2.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_full_bw                           [BwDemod]
% 2.33/0.98  --sup_immed_triv                        [TrivRules]
% 2.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_immed_bw_main                     []
% 2.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.98  
% 2.33/0.98  ------ Combination Options
% 2.33/0.98  
% 2.33/0.98  --comb_res_mult                         3
% 2.33/0.98  --comb_sup_mult                         2
% 2.33/0.98  --comb_inst_mult                        10
% 2.33/0.98  
% 2.33/0.98  ------ Debug Options
% 2.33/0.98  
% 2.33/0.98  --dbg_backtrace                         false
% 2.33/0.98  --dbg_dump_prop_clauses                 false
% 2.33/0.98  --dbg_dump_prop_clauses_file            -
% 2.33/0.98  --dbg_out_stat                          false
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  ------ Proving...
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  % SZS status Theorem for theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  fof(f4,axiom,(
% 2.33/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f34,plain,(
% 2.33/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.33/0.98    inference(nnf_transformation,[],[f4])).
% 2.33/0.98  
% 2.33/0.98  fof(f35,plain,(
% 2.33/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.33/0.98    inference(flattening,[],[f34])).
% 2.33/0.98  
% 2.33/0.98  fof(f49,plain,(
% 2.33/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.33/0.98    inference(cnf_transformation,[],[f35])).
% 2.33/0.98  
% 2.33/0.98  fof(f72,plain,(
% 2.33/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.33/0.98    inference(equality_resolution,[],[f49])).
% 2.33/0.98  
% 2.33/0.98  fof(f12,axiom,(
% 2.33/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f22,plain,(
% 2.33/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.33/0.98    inference(ennf_transformation,[],[f12])).
% 2.33/0.98  
% 2.33/0.98  fof(f23,plain,(
% 2.33/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.33/0.98    inference(flattening,[],[f22])).
% 2.33/0.98  
% 2.33/0.98  fof(f59,plain,(
% 2.33/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f23])).
% 2.33/0.98  
% 2.33/0.98  fof(f13,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f24,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f13])).
% 2.33/0.98  
% 2.33/0.98  fof(f25,plain,(
% 2.33/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(flattening,[],[f24])).
% 2.33/0.98  
% 2.33/0.98  fof(f37,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(nnf_transformation,[],[f25])).
% 2.33/0.98  
% 2.33/0.98  fof(f62,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f37])).
% 2.33/0.98  
% 2.33/0.98  fof(f14,conjecture,(
% 2.33/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f15,negated_conjecture,(
% 2.33/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.33/0.98    inference(negated_conjecture,[],[f14])).
% 2.33/0.98  
% 2.33/0.98  fof(f26,plain,(
% 2.33/0.98    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.33/0.98    inference(ennf_transformation,[],[f15])).
% 2.33/0.98  
% 2.33/0.98  fof(f27,plain,(
% 2.33/0.98    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.33/0.98    inference(flattening,[],[f26])).
% 2.33/0.98  
% 2.33/0.98  fof(f38,plain,(
% 2.33/0.98    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f39,plain,(
% 2.33/0.98    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)) & r1_tarski(k2_relat_1(sK2),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f38])).
% 2.33/0.98  
% 2.33/0.98  fof(f69,plain,(
% 2.33/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2)),
% 2.33/0.98    inference(cnf_transformation,[],[f39])).
% 2.33/0.98  
% 2.33/0.98  fof(f67,plain,(
% 2.33/0.98    v1_funct_1(sK2)),
% 2.33/0.98    inference(cnf_transformation,[],[f39])).
% 2.33/0.98  
% 2.33/0.98  fof(f11,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f21,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.98    inference(ennf_transformation,[],[f11])).
% 2.33/0.98  
% 2.33/0.98  fof(f58,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f21])).
% 2.33/0.98  
% 2.33/0.98  fof(f68,plain,(
% 2.33/0.98    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.33/0.98    inference(cnf_transformation,[],[f39])).
% 2.33/0.98  
% 2.33/0.98  fof(f9,axiom,(
% 2.33/0.98    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f20,plain,(
% 2.33/0.98    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.33/0.98    inference(ennf_transformation,[],[f9])).
% 2.33/0.98  
% 2.33/0.98  fof(f55,plain,(
% 2.33/0.98    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f20])).
% 2.33/0.98  
% 2.33/0.98  fof(f66,plain,(
% 2.33/0.98    v1_relat_1(sK2)),
% 2.33/0.98    inference(cnf_transformation,[],[f39])).
% 2.33/0.98  
% 2.33/0.98  fof(f6,axiom,(
% 2.33/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f36,plain,(
% 2.33/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.33/0.98    inference(nnf_transformation,[],[f6])).
% 2.33/0.98  
% 2.33/0.98  fof(f52,plain,(
% 2.33/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f36])).
% 2.33/0.98  
% 2.33/0.98  fof(f5,axiom,(
% 2.33/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f50,plain,(
% 2.33/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f5])).
% 2.33/0.98  
% 2.33/0.98  fof(f51,plain,(
% 2.33/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f36])).
% 2.33/0.98  
% 2.33/0.98  fof(f3,axiom,(
% 2.33/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f32,plain,(
% 2.33/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/0.98    inference(nnf_transformation,[],[f3])).
% 2.33/0.98  
% 2.33/0.98  fof(f33,plain,(
% 2.33/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/0.98    inference(flattening,[],[f32])).
% 2.33/0.98  
% 2.33/0.98  fof(f46,plain,(
% 2.33/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f33])).
% 2.33/0.98  
% 2.33/0.98  fof(f2,axiom,(
% 2.33/0.98    v1_xboole_0(k1_xboole_0)),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f43,plain,(
% 2.33/0.98    v1_xboole_0(k1_xboole_0)),
% 2.33/0.98    inference(cnf_transformation,[],[f2])).
% 2.33/0.98  
% 2.33/0.98  fof(f8,axiom,(
% 2.33/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f19,plain,(
% 2.33/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.33/0.98    inference(ennf_transformation,[],[f8])).
% 2.33/0.98  
% 2.33/0.98  fof(f54,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f19])).
% 2.33/0.98  
% 2.33/0.98  fof(f1,axiom,(
% 2.33/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f16,plain,(
% 2.33/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.33/0.98    inference(ennf_transformation,[],[f1])).
% 2.33/0.98  
% 2.33/0.98  fof(f28,plain,(
% 2.33/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.33/0.98    inference(nnf_transformation,[],[f16])).
% 2.33/0.98  
% 2.33/0.98  fof(f29,plain,(
% 2.33/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.33/0.98    inference(rectify,[],[f28])).
% 2.33/0.98  
% 2.33/0.98  fof(f30,plain,(
% 2.33/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.33/0.98    introduced(choice_axiom,[])).
% 2.33/0.98  
% 2.33/0.98  fof(f31,plain,(
% 2.33/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.33/0.98  
% 2.33/0.98  fof(f41,plain,(
% 2.33/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f31])).
% 2.33/0.98  
% 2.33/0.98  fof(f63,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f37])).
% 2.33/0.98  
% 2.33/0.98  fof(f77,plain,(
% 2.33/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.33/0.98    inference(equality_resolution,[],[f63])).
% 2.33/0.98  
% 2.33/0.98  fof(f65,plain,(
% 2.33/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(cnf_transformation,[],[f37])).
% 2.33/0.98  
% 2.33/0.98  fof(f74,plain,(
% 2.33/0.98    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.98    inference(equality_resolution,[],[f65])).
% 2.33/0.98  
% 2.33/0.98  fof(f75,plain,(
% 2.33/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.33/0.98    inference(equality_resolution,[],[f74])).
% 2.33/0.98  
% 2.33/0.98  fof(f48,plain,(
% 2.33/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.33/0.98    inference(cnf_transformation,[],[f35])).
% 2.33/0.98  
% 2.33/0.98  fof(f73,plain,(
% 2.33/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.33/0.98    inference(equality_resolution,[],[f48])).
% 2.33/0.98  
% 2.33/0.98  fof(f47,plain,(
% 2.33/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.33/0.98    inference(cnf_transformation,[],[f35])).
% 2.33/0.98  
% 2.33/0.98  fof(f10,axiom,(
% 2.33/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.33/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.98  
% 2.33/0.98  fof(f56,plain,(
% 2.33/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.33/0.98    inference(cnf_transformation,[],[f10])).
% 2.33/0.98  
% 2.33/0.98  cnf(c_7,plain,
% 2.33/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_19,plain,
% 2.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.33/0.98      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 2.33/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1049,plain,
% 2.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 2.33/0.98      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1769,plain,
% 2.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.33/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.33/0.98      | r1_tarski(k2_relat_1(X0),X2) != iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_7,c_1049]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_23,plain,
% 2.33/0.98      ( v1_funct_2(X0,X1,X2)
% 2.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.33/0.98      | k1_xboole_0 = X2 ),
% 2.33/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_26,negated_conjecture,
% 2.33/0.98      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 2.33/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | ~ v1_funct_1(sK2) ),
% 2.33/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_28,negated_conjecture,
% 2.33/0.98      ( v1_funct_1(sK2) ),
% 2.33/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_141,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_26,c_28]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_142,negated_conjecture,
% 2.33/0.98      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
% 2.33/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_141]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_418,plain,
% 2.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | k1_relset_1(X1,X2,X0) != X1
% 2.33/0.98      | k1_relat_1(sK2) != X1
% 2.33/0.98      | sK1 != X2
% 2.33/0.98      | sK2 != X0
% 2.33/0.98      | k1_xboole_0 = X2 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_142]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_419,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | k1_relset_1(k1_relat_1(sK2),sK1,sK2) != k1_relat_1(sK2)
% 2.33/0.98      | k1_xboole_0 = sK1 ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_418]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_18,plain,
% 2.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_427,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | k1_xboole_0 = sK1 ),
% 2.33/0.98      inference(forward_subsumption_resolution,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_419,c_18]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1043,plain,
% 2.33/0.98      ( k1_xboole_0 = sK1
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2397,plain,
% 2.33/0.98      ( sK1 = k1_xboole_0
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.33/0.98      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_1769,c_1043]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_27,negated_conjecture,
% 2.33/0.98      ( r1_tarski(k2_relat_1(sK2),sK1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_15,plain,
% 2.33/0.98      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 2.33/0.98      | ~ v1_relat_1(X0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_29,negated_conjecture,
% 2.33/0.98      ( v1_relat_1(sK2) ),
% 2.33/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_343,plain,
% 2.33/0.98      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 2.33/0.98      | sK2 != X0 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_344,plain,
% 2.33/0.98      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_343]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_610,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1269,plain,
% 2.33/0.98      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_610]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1363,plain,
% 2.33/0.98      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1269]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_609,plain,( X0 = X0 ),theory(equality) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1364,plain,
% 2.33/0.98      ( sK1 = sK1 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_609]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_11,plain,
% 2.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1217,plain,
% 2.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.98      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1443,plain,
% 2.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.33/0.98      | ~ r1_tarski(sK2,k2_zfmisc_1(X0,X1)) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1217]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1544,plain,
% 2.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.33/0.98      | ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1443]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1245,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 2.33/0.98      | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1481,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK2))))
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 2.33/0.98      | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1245]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2340,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1481]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2616,plain,
% 2.33/0.98      ( sK1 = k1_xboole_0 ),
% 2.33/0.98      inference(global_propositional_subsumption,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_2397,c_27,c_344,c_427,c_1363,c_1364,c_1544,c_2340]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1048,plain,
% 2.33/0.98      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2623,plain,
% 2.33/0.98      ( r1_tarski(k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 2.33/0.98      inference(demodulation,[status(thm)],[c_2616,c_1048]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_10,plain,
% 2.33/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.33/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1054,plain,
% 2.33/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_12,plain,
% 2.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1052,plain,
% 2.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.33/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1473,plain,
% 2.33/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_1054,c_1052]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_4,plain,
% 2.33/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.33/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1056,plain,
% 2.33/0.98      ( X0 = X1
% 2.33/0.98      | r1_tarski(X1,X0) != iProver_top
% 2.33/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1866,plain,
% 2.33/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_1473,c_1056]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2656,plain,
% 2.33/0.98      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_2623,c_1866]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1047,plain,
% 2.33/0.98      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2775,plain,
% 2.33/0.98      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) = iProver_top ),
% 2.33/0.98      inference(demodulation,[status(thm)],[c_2656,c_1047]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2777,plain,
% 2.33/0.98      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.33/0.98      inference(demodulation,[status(thm)],[c_2775,c_7]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2800,plain,
% 2.33/0.98      ( sK2 = k1_xboole_0 ),
% 2.33/0.98      inference(superposition,[status(thm)],[c_2777,c_1866]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2346,plain,
% 2.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
% 2.33/0.98      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2340]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_3,plain,
% 2.33/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.33/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_14,plain,
% 2.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.33/0.98      | ~ r2_hidden(X2,X0)
% 2.33/0.98      | ~ v1_xboole_0(X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_199,plain,
% 2.33/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.33/0.98      inference(prop_impl,[status(thm)],[c_11]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_200,plain,
% 2.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.33/0.98      inference(renaming,[status(thm)],[c_199]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_254,plain,
% 2.33/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.33/0.98      inference(bin_hyper_res,[status(thm)],[c_14,c_200]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_352,plain,
% 2.33/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_254]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_353,plain,
% 2.33/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_352]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2290,plain,
% 2.33/0.98      ( ~ r2_hidden(sK0(sK2,k2_zfmisc_1(X0,X1)),sK2)
% 2.33/0.98      | ~ r1_tarski(sK2,k1_xboole_0) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_353]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2291,plain,
% 2.33/0.98      ( r2_hidden(sK0(sK2,k2_zfmisc_1(X0,X1)),sK2) != iProver_top
% 2.33/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2290]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2293,plain,
% 2.33/0.98      ( r2_hidden(sK0(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2) != iProver_top
% 2.33/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_2291]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2188,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.33/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2189,plain,
% 2.33/0.98      ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2)
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_2188]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1807,plain,
% 2.33/0.98      ( k1_relset_1(k1_xboole_0,sK1,sK2) != X0
% 2.33/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.33/0.98      | k1_xboole_0 != X0 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_610]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_2187,plain,
% 2.33/0.98      ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_relat_1(sK2)
% 2.33/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) = k1_xboole_0
% 2.33/0.98      | k1_xboole_0 != k1_relat_1(sK2) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1807]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1545,plain,
% 2.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 2.33/0.98      | r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1544]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1,plain,
% 2.33/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.33/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1523,plain,
% 2.33/0.98      ( r2_hidden(sK0(sK2,k2_zfmisc_1(X0,X1)),sK2)
% 2.33/0.98      | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1534,plain,
% 2.33/0.98      ( r2_hidden(sK0(sK2,k2_zfmisc_1(X0,X1)),sK2) = iProver_top
% 2.33/0.98      | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1523]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1536,plain,
% 2.33/0.98      ( r2_hidden(sK0(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2) = iProver_top
% 2.33/0.98      | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1534]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1444,plain,
% 2.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 2.33/0.98      | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1443]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1446,plain,
% 2.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 2.33/0.98      | r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1444]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1372,plain,
% 2.33/0.98      ( k1_relat_1(X0) != X1
% 2.33/0.98      | k1_xboole_0 != X1
% 2.33/0.98      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_610]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1373,plain,
% 2.33/0.98      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.33/0.98      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.33/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1372]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_616,plain,
% 2.33/0.98      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.33/0.98      theory(equality) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1293,plain,
% 2.33/0.98      ( k1_relat_1(sK2) = k1_relat_1(X0) | sK2 != X0 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_616]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1295,plain,
% 2.33/0.98      ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1293]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1270,plain,
% 2.33/0.98      ( k1_relat_1(sK2) != X0
% 2.33/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 2.33/0.98      | k1_xboole_0 != X0 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_610]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1292,plain,
% 2.33/0.98      ( k1_relat_1(sK2) != k1_relat_1(X0)
% 2.33/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 2.33/0.98      | k1_xboole_0 != k1_relat_1(X0) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1270]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1294,plain,
% 2.33/0.98      ( k1_relat_1(sK2) != k1_relat_1(k1_xboole_0)
% 2.33/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 2.33/0.98      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1292]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1246,plain,
% 2.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 2.33/0.98      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_1248,plain,
% 2.33/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) = iProver_top
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 2.33/0.98      | r1_tarski(k2_relat_1(sK2),sK1) != iProver_top ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_1246]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_22,plain,
% 2.33/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.33/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.33/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.33/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_402,plain,
% 2.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.33/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.33/0.98      | k1_relat_1(sK2) != k1_xboole_0
% 2.33/0.98      | sK1 != X1
% 2.33/0.98      | sK2 != X0 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_142]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_403,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.33/0.98      | k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 2.33/0.98      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_402]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_404,plain,
% 2.33/0.98      ( k1_relset_1(k1_xboole_0,sK1,sK2) != k1_xboole_0
% 2.33/0.98      | k1_relat_1(sK2) != k1_xboole_0
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) != iProver_top
% 2.33/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_20,plain,
% 2.33/0.98      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.33/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.33/0.98      | k1_xboole_0 = X0 ),
% 2.33/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_375,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.33/0.98      | k1_relat_1(sK2) != X0
% 2.33/0.98      | sK1 != k1_xboole_0
% 2.33/0.98      | sK2 != k1_xboole_0
% 2.33/0.98      | k1_xboole_0 = X0 ),
% 2.33/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_142]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_376,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
% 2.33/0.98      | sK1 != k1_xboole_0
% 2.33/0.98      | sK2 != k1_xboole_0
% 2.33/0.98      | k1_xboole_0 = k1_relat_1(sK2) ),
% 2.33/0.98      inference(unflattening,[status(thm)],[c_375]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_388,plain,
% 2.33/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
% 2.33/0.98      | sK1 != k1_xboole_0
% 2.33/0.98      | sK2 != k1_xboole_0
% 2.33/0.98      | k1_xboole_0 = k1_relat_1(sK2) ),
% 2.33/0.98      inference(forward_subsumption_resolution,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_376,c_10]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_345,plain,
% 2.33/0.98      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_8,plain,
% 2.33/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.33/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_75,plain,
% 2.33/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_9,plain,
% 2.33/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.33/0.98      | k1_xboole_0 = X1
% 2.33/0.98      | k1_xboole_0 = X0 ),
% 2.33/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_74,plain,
% 2.33/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.33/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 2.33/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_17,plain,
% 2.33/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.33/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(c_32,plain,
% 2.33/0.98      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 2.33/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.33/0.98  
% 2.33/0.98  cnf(contradiction,plain,
% 2.33/0.98      ( $false ),
% 2.33/0.98      inference(minisat,
% 2.33/0.98                [status(thm)],
% 2.33/0.98                [c_2800,c_2777,c_2346,c_2340,c_2293,c_2189,c_2187,c_1545,
% 2.33/0.98                 c_1544,c_1536,c_1446,c_1373,c_1364,c_1363,c_1295,c_1294,
% 2.33/0.98                 c_1248,c_427,c_404,c_388,c_345,c_344,c_75,c_74,c_17,
% 2.33/0.98                 c_32,c_27]) ).
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/0.98  
% 2.33/0.98  ------                               Statistics
% 2.33/0.98  
% 2.33/0.98  ------ General
% 2.33/0.98  
% 2.33/0.98  abstr_ref_over_cycles:                  0
% 2.33/0.98  abstr_ref_under_cycles:                 0
% 2.33/0.98  gc_basic_clause_elim:                   0
% 2.33/0.98  forced_gc_time:                         0
% 2.33/0.98  parsing_time:                           0.008
% 2.33/0.98  unif_index_cands_time:                  0.
% 2.33/0.98  unif_index_add_time:                    0.
% 2.33/0.98  orderings_time:                         0.
% 2.33/0.98  out_proof_time:                         0.008
% 2.33/0.98  total_time:                             0.121
% 2.33/0.98  num_of_symbols:                         47
% 2.33/0.98  num_of_terms:                           2348
% 2.33/0.98  
% 2.33/0.98  ------ Preprocessing
% 2.33/0.98  
% 2.33/0.98  num_of_splits:                          0
% 2.33/0.98  num_of_split_atoms:                     0
% 2.33/0.98  num_of_reused_defs:                     0
% 2.33/0.98  num_eq_ax_congr_red:                    11
% 2.33/0.98  num_of_sem_filtered_clauses:            2
% 2.33/0.98  num_of_subtypes:                        0
% 2.33/0.98  monotx_restored_types:                  0
% 2.33/0.98  sat_num_of_epr_types:                   0
% 2.33/0.98  sat_num_of_non_cyclic_types:            0
% 2.33/0.98  sat_guarded_non_collapsed_types:        0
% 2.33/0.98  num_pure_diseq_elim:                    0
% 2.33/0.98  simp_replaced_by:                       0
% 2.33/0.98  res_preprocessed:                       116
% 2.33/0.98  prep_upred:                             0
% 2.33/0.98  prep_unflattend:                        28
% 2.33/0.98  smt_new_axioms:                         0
% 2.33/0.98  pred_elim_cands:                        3
% 2.33/0.98  pred_elim:                              3
% 2.33/0.98  pred_elim_cl:                           6
% 2.33/0.98  pred_elim_cycles:                       5
% 2.33/0.98  merged_defs:                            8
% 2.33/0.98  merged_defs_ncl:                        0
% 2.33/0.98  bin_hyper_res:                          9
% 2.33/0.98  prep_cycles:                            4
% 2.33/0.98  pred_elim_time:                         0.008
% 2.33/0.98  splitting_time:                         0.
% 2.33/0.98  sem_filter_time:                        0.
% 2.33/0.98  monotx_time:                            0.001
% 2.33/0.98  subtype_inf_time:                       0.
% 2.33/0.98  
% 2.33/0.98  ------ Problem properties
% 2.33/0.98  
% 2.33/0.98  clauses:                                22
% 2.33/0.98  conjectures:                            1
% 2.33/0.98  epr:                                    4
% 2.33/0.98  horn:                                   20
% 2.33/0.98  ground:                                 7
% 2.33/0.98  unary:                                  8
% 2.33/0.98  binary:                                 7
% 2.33/0.98  lits:                                   45
% 2.33/0.98  lits_eq:                                15
% 2.33/0.98  fd_pure:                                0
% 2.33/0.98  fd_pseudo:                              0
% 2.33/0.98  fd_cond:                                1
% 2.33/0.98  fd_pseudo_cond:                         1
% 2.33/0.98  ac_symbols:                             0
% 2.33/0.98  
% 2.33/0.98  ------ Propositional Solver
% 2.33/0.98  
% 2.33/0.98  prop_solver_calls:                      27
% 2.33/0.98  prop_fast_solver_calls:                 610
% 2.33/0.98  smt_solver_calls:                       0
% 2.33/0.98  smt_fast_solver_calls:                  0
% 2.33/0.98  prop_num_of_clauses:                    867
% 2.33/0.98  prop_preprocess_simplified:             3789
% 2.33/0.98  prop_fo_subsumed:                       3
% 2.33/0.98  prop_solver_time:                       0.
% 2.33/0.98  smt_solver_time:                        0.
% 2.33/0.98  smt_fast_solver_time:                   0.
% 2.33/0.98  prop_fast_solver_time:                  0.
% 2.33/0.98  prop_unsat_core_time:                   0.
% 2.33/0.98  
% 2.33/0.98  ------ QBF
% 2.33/0.98  
% 2.33/0.98  qbf_q_res:                              0
% 2.33/0.98  qbf_num_tautologies:                    0
% 2.33/0.98  qbf_prep_cycles:                        0
% 2.33/0.98  
% 2.33/0.98  ------ BMC1
% 2.33/0.98  
% 2.33/0.98  bmc1_current_bound:                     -1
% 2.33/0.98  bmc1_last_solved_bound:                 -1
% 2.33/0.98  bmc1_unsat_core_size:                   -1
% 2.33/0.98  bmc1_unsat_core_parents_size:           -1
% 2.33/0.98  bmc1_merge_next_fun:                    0
% 2.33/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.33/0.98  
% 2.33/0.98  ------ Instantiation
% 2.33/0.98  
% 2.33/0.98  inst_num_of_clauses:                    274
% 2.33/0.98  inst_num_in_passive:                    43
% 2.33/0.98  inst_num_in_active:                     136
% 2.33/0.98  inst_num_in_unprocessed:                95
% 2.33/0.98  inst_num_of_loops:                      210
% 2.33/0.98  inst_num_of_learning_restarts:          0
% 2.33/0.98  inst_num_moves_active_passive:          71
% 2.33/0.98  inst_lit_activity:                      0
% 2.33/0.98  inst_lit_activity_moves:                0
% 2.33/0.98  inst_num_tautologies:                   0
% 2.33/0.98  inst_num_prop_implied:                  0
% 2.33/0.98  inst_num_existing_simplified:           0
% 2.33/0.98  inst_num_eq_res_simplified:             0
% 2.33/0.98  inst_num_child_elim:                    0
% 2.33/0.98  inst_num_of_dismatching_blockings:      69
% 2.33/0.98  inst_num_of_non_proper_insts:           257
% 2.33/0.98  inst_num_of_duplicates:                 0
% 2.33/0.98  inst_inst_num_from_inst_to_res:         0
% 2.33/0.98  inst_dismatching_checking_time:         0.
% 2.33/0.98  
% 2.33/0.98  ------ Resolution
% 2.33/0.98  
% 2.33/0.98  res_num_of_clauses:                     0
% 2.33/0.98  res_num_in_passive:                     0
% 2.33/0.98  res_num_in_active:                      0
% 2.33/0.98  res_num_of_loops:                       120
% 2.33/0.98  res_forward_subset_subsumed:            12
% 2.33/0.98  res_backward_subset_subsumed:           0
% 2.33/0.98  res_forward_subsumed:                   0
% 2.33/0.98  res_backward_subsumed:                  0
% 2.33/0.98  res_forward_subsumption_resolution:     2
% 2.33/0.98  res_backward_subsumption_resolution:    0
% 2.33/0.98  res_clause_to_clause_subsumption:       183
% 2.33/0.98  res_orphan_elimination:                 0
% 2.33/0.98  res_tautology_del:                      32
% 2.33/0.98  res_num_eq_res_simplified:              0
% 2.33/0.98  res_num_sel_changes:                    0
% 2.33/0.98  res_moves_from_active_to_pass:          0
% 2.33/0.98  
% 2.33/0.98  ------ Superposition
% 2.33/0.98  
% 2.33/0.98  sup_time_total:                         0.
% 2.33/0.98  sup_time_generating:                    0.
% 2.33/0.98  sup_time_sim_full:                      0.
% 2.33/0.98  sup_time_sim_immed:                     0.
% 2.33/0.98  
% 2.33/0.98  sup_num_of_clauses:                     44
% 2.33/0.98  sup_num_in_active:                      32
% 2.33/0.98  sup_num_in_passive:                     12
% 2.33/0.98  sup_num_of_loops:                       41
% 2.33/0.98  sup_fw_superposition:                   40
% 2.33/0.98  sup_bw_superposition:                   19
% 2.33/0.98  sup_immediate_simplified:               17
% 2.33/0.98  sup_given_eliminated:                   2
% 2.33/0.98  comparisons_done:                       0
% 2.33/0.98  comparisons_avoided:                    0
% 2.33/0.98  
% 2.33/0.98  ------ Simplifications
% 2.33/0.98  
% 2.33/0.98  
% 2.33/0.98  sim_fw_subset_subsumed:                 2
% 2.33/0.98  sim_bw_subset_subsumed:                 3
% 2.33/0.98  sim_fw_subsumed:                        8
% 2.33/0.98  sim_bw_subsumed:                        0
% 2.33/0.98  sim_fw_subsumption_res:                 0
% 2.33/0.98  sim_bw_subsumption_res:                 0
% 2.33/0.98  sim_tautology_del:                      4
% 2.33/0.98  sim_eq_tautology_del:                   4
% 2.33/0.98  sim_eq_res_simp:                        1
% 2.33/0.98  sim_fw_demodulated:                     6
% 2.33/0.98  sim_bw_demodulated:                     10
% 2.33/0.98  sim_light_normalised:                   9
% 2.33/0.98  sim_joinable_taut:                      0
% 2.33/0.98  sim_joinable_simp:                      0
% 2.33/0.98  sim_ac_normalised:                      0
% 2.33/0.98  sim_smt_subsumption:                    0
% 2.33/0.98  
%------------------------------------------------------------------------------
