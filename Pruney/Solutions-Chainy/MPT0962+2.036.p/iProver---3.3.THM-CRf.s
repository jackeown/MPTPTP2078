%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:15 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 873 expanded)
%              Number of clauses        :   87 ( 323 expanded)
%              Number of leaves         :   17 ( 169 expanded)
%              Depth                    :   20
%              Number of atoms          :  458 (3661 expanded)
%              Number of equality atoms :  228 ( 967 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
        | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
        | ~ v1_funct_1(sK3) )
      & r1_tarski(k2_relat_1(sK3),sK2)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
      | ~ v1_funct_1(sK3) )
    & r1_tarski(k2_relat_1(sK3),sK2)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f35])).

fof(f67,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f30])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f15,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK1(X0,X1),X0,X1)
        & v1_funct_1(sK1(X0,X1))
        & v1_relat_1(sK1(X0,X1))
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK1(X0,X1),X0,X1)
      & v1_funct_1(sK1(X0,X1))
      & v1_relat_1(sK1(X0,X1))
      & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f33])).

fof(f63,plain,(
    ! [X0,X1] : v1_funct_2(sK1(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X0,X1] : m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_153,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_29])).

cnf(c_154,negated_conjecture,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_relat_1(sK3) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_154])).

cnf(c_529,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_relset_1(k1_relat_1(sK3),sK2,sK3) != k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_537,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_529,c_12])).

cnf(c_1180,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_2066,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1180])).

cnf(c_30,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1417,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_762,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1372,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1452,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_761,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1453,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1369,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),X1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1416,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_1519,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_2150,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2066,c_30,c_28,c_537,c_1417,c_1452,c_1453,c_1519])).

cnf(c_1185,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2157,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2150,c_1185])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_354,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_16,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | X1 != X0
    | sK0(X1) != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_354,c_16])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_1183,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_2067,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1183])).

cnf(c_2598,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2157,c_2067])).

cnf(c_1192,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1188,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1983,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1188])).

cnf(c_2964,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1983])).

cnf(c_3375,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_2964])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1984,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1188])).

cnf(c_2986,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2598,c_1984])).

cnf(c_31,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_89,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_91,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_1679,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_23,plain,
    ( v1_funct_2(sK1(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_541,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | sK1(X0,X1) != sK3
    | k1_relat_1(sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_154])).

cnf(c_542,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | sK1(k1_relat_1(sK3),sK2) != sK3 ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_1179,plain,
    ( sK1(k1_relat_1(sK3),sK2) != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_2156,plain,
    ( sK1(k1_relat_1(sK3),k1_xboole_0) != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2150,c_1179])).

cnf(c_26,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1186,plain,
    ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1807,plain,
    ( m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1186])).

cnf(c_1907,plain,
    ( sK1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1807,c_1183])).

cnf(c_2162,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2156,c_4,c_1907])).

cnf(c_1649,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_2270,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_2271,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_2935,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_2936,plain,
    ( k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2935])).

cnf(c_3136,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2986])).

cnf(c_3238,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2986,c_31,c_91,c_1679,c_2162,c_2271,c_2936,c_3136])).

cnf(c_763,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1424,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),X2)
    | X2 != X1
    | k1_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1425,plain,
    ( X0 != X1
    | k1_relat_1(sK3) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1424])).

cnf(c_1427,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_17,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_447,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_relat_1(sK3) != X0
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_154])).

cnf(c_448,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_1182,plain,
    ( sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_1283,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1182,c_4])).

cnf(c_84,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_86,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_1386,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
    | sK3 != k1_xboole_0
    | sK2 != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1283,c_86,c_91])).

cnf(c_1387,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1386])).

cnf(c_1388,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1387])).

cnf(c_88,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_87,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3375,c_3238,c_2936,c_2271,c_1679,c_1519,c_1453,c_1452,c_1427,c_1417,c_1388,c_537,c_91,c_88,c_87,c_28,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:12:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.31/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/0.98  
% 2.31/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.31/0.98  
% 2.31/0.98  ------  iProver source info
% 2.31/0.98  
% 2.31/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.31/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.31/0.98  git: non_committed_changes: false
% 2.31/0.98  git: last_make_outside_of_git: false
% 2.31/0.98  
% 2.31/0.98  ------ 
% 2.31/0.98  
% 2.31/0.98  ------ Input Options
% 2.31/0.98  
% 2.31/0.98  --out_options                           all
% 2.31/0.98  --tptp_safe_out                         true
% 2.31/0.98  --problem_path                          ""
% 2.31/0.98  --include_path                          ""
% 2.31/0.98  --clausifier                            res/vclausify_rel
% 2.31/0.98  --clausifier_options                    --mode clausify
% 2.31/0.98  --stdin                                 false
% 2.31/0.98  --stats_out                             all
% 2.31/0.98  
% 2.31/0.98  ------ General Options
% 2.31/0.98  
% 2.31/0.98  --fof                                   false
% 2.31/0.98  --time_out_real                         305.
% 2.31/0.98  --time_out_virtual                      -1.
% 2.31/0.98  --symbol_type_check                     false
% 2.31/0.98  --clausify_out                          false
% 2.31/0.98  --sig_cnt_out                           false
% 2.31/0.98  --trig_cnt_out                          false
% 2.31/0.98  --trig_cnt_out_tolerance                1.
% 2.31/0.98  --trig_cnt_out_sk_spl                   false
% 2.31/0.98  --abstr_cl_out                          false
% 2.31/0.98  
% 2.31/0.98  ------ Global Options
% 2.31/0.98  
% 2.31/0.98  --schedule                              default
% 2.31/0.98  --add_important_lit                     false
% 2.31/0.98  --prop_solver_per_cl                    1000
% 2.31/0.98  --min_unsat_core                        false
% 2.31/0.98  --soft_assumptions                      false
% 2.31/0.98  --soft_lemma_size                       3
% 2.31/0.98  --prop_impl_unit_size                   0
% 2.31/0.98  --prop_impl_unit                        []
% 2.31/0.98  --share_sel_clauses                     true
% 2.31/0.98  --reset_solvers                         false
% 2.31/0.98  --bc_imp_inh                            [conj_cone]
% 2.31/0.98  --conj_cone_tolerance                   3.
% 2.31/0.98  --extra_neg_conj                        none
% 2.31/0.98  --large_theory_mode                     true
% 2.31/0.98  --prolific_symb_bound                   200
% 2.31/0.98  --lt_threshold                          2000
% 2.31/0.98  --clause_weak_htbl                      true
% 2.31/0.98  --gc_record_bc_elim                     false
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing Options
% 2.31/0.98  
% 2.31/0.98  --preprocessing_flag                    true
% 2.31/0.98  --time_out_prep_mult                    0.1
% 2.31/0.98  --splitting_mode                        input
% 2.31/0.98  --splitting_grd                         true
% 2.31/0.98  --splitting_cvd                         false
% 2.31/0.98  --splitting_cvd_svl                     false
% 2.31/0.98  --splitting_nvd                         32
% 2.31/0.98  --sub_typing                            true
% 2.31/0.98  --prep_gs_sim                           true
% 2.31/0.98  --prep_unflatten                        true
% 2.31/0.98  --prep_res_sim                          true
% 2.31/0.98  --prep_upred                            true
% 2.31/0.98  --prep_sem_filter                       exhaustive
% 2.31/0.98  --prep_sem_filter_out                   false
% 2.31/0.98  --pred_elim                             true
% 2.31/0.98  --res_sim_input                         true
% 2.31/0.98  --eq_ax_congr_red                       true
% 2.31/0.98  --pure_diseq_elim                       true
% 2.31/0.98  --brand_transform                       false
% 2.31/0.98  --non_eq_to_eq                          false
% 2.31/0.98  --prep_def_merge                        true
% 2.31/0.98  --prep_def_merge_prop_impl              false
% 2.31/0.98  --prep_def_merge_mbd                    true
% 2.31/0.98  --prep_def_merge_tr_red                 false
% 2.31/0.98  --prep_def_merge_tr_cl                  false
% 2.31/0.98  --smt_preprocessing                     true
% 2.31/0.98  --smt_ac_axioms                         fast
% 2.31/0.98  --preprocessed_out                      false
% 2.31/0.98  --preprocessed_stats                    false
% 2.31/0.98  
% 2.31/0.98  ------ Abstraction refinement Options
% 2.31/0.98  
% 2.31/0.98  --abstr_ref                             []
% 2.31/0.98  --abstr_ref_prep                        false
% 2.31/0.98  --abstr_ref_until_sat                   false
% 2.31/0.98  --abstr_ref_sig_restrict                funpre
% 2.31/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.98  --abstr_ref_under                       []
% 2.31/0.98  
% 2.31/0.98  ------ SAT Options
% 2.31/0.98  
% 2.31/0.98  --sat_mode                              false
% 2.31/0.98  --sat_fm_restart_options                ""
% 2.31/0.98  --sat_gr_def                            false
% 2.31/0.98  --sat_epr_types                         true
% 2.31/0.98  --sat_non_cyclic_types                  false
% 2.31/0.98  --sat_finite_models                     false
% 2.31/0.98  --sat_fm_lemmas                         false
% 2.31/0.98  --sat_fm_prep                           false
% 2.31/0.98  --sat_fm_uc_incr                        true
% 2.31/0.98  --sat_out_model                         small
% 2.31/0.98  --sat_out_clauses                       false
% 2.31/0.98  
% 2.31/0.98  ------ QBF Options
% 2.31/0.98  
% 2.31/0.98  --qbf_mode                              false
% 2.31/0.98  --qbf_elim_univ                         false
% 2.31/0.98  --qbf_dom_inst                          none
% 2.31/0.98  --qbf_dom_pre_inst                      false
% 2.31/0.98  --qbf_sk_in                             false
% 2.31/0.98  --qbf_pred_elim                         true
% 2.31/0.98  --qbf_split                             512
% 2.31/0.98  
% 2.31/0.98  ------ BMC1 Options
% 2.31/0.98  
% 2.31/0.98  --bmc1_incremental                      false
% 2.31/0.98  --bmc1_axioms                           reachable_all
% 2.31/0.98  --bmc1_min_bound                        0
% 2.31/0.98  --bmc1_max_bound                        -1
% 2.31/0.98  --bmc1_max_bound_default                -1
% 2.31/0.98  --bmc1_symbol_reachability              true
% 2.31/0.98  --bmc1_property_lemmas                  false
% 2.31/0.98  --bmc1_k_induction                      false
% 2.31/0.98  --bmc1_non_equiv_states                 false
% 2.31/0.98  --bmc1_deadlock                         false
% 2.31/0.98  --bmc1_ucm                              false
% 2.31/0.98  --bmc1_add_unsat_core                   none
% 2.31/0.98  --bmc1_unsat_core_children              false
% 2.31/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.98  --bmc1_out_stat                         full
% 2.31/0.98  --bmc1_ground_init                      false
% 2.31/0.98  --bmc1_pre_inst_next_state              false
% 2.31/0.98  --bmc1_pre_inst_state                   false
% 2.31/0.98  --bmc1_pre_inst_reach_state             false
% 2.31/0.98  --bmc1_out_unsat_core                   false
% 2.31/0.98  --bmc1_aig_witness_out                  false
% 2.31/0.98  --bmc1_verbose                          false
% 2.31/0.98  --bmc1_dump_clauses_tptp                false
% 2.31/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.98  --bmc1_dump_file                        -
% 2.31/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.98  --bmc1_ucm_extend_mode                  1
% 2.31/0.98  --bmc1_ucm_init_mode                    2
% 2.31/0.98  --bmc1_ucm_cone_mode                    none
% 2.31/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.98  --bmc1_ucm_relax_model                  4
% 2.31/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.98  --bmc1_ucm_layered_model                none
% 2.31/0.98  --bmc1_ucm_max_lemma_size               10
% 2.31/0.98  
% 2.31/0.98  ------ AIG Options
% 2.31/0.98  
% 2.31/0.98  --aig_mode                              false
% 2.31/0.98  
% 2.31/0.98  ------ Instantiation Options
% 2.31/0.98  
% 2.31/0.98  --instantiation_flag                    true
% 2.31/0.98  --inst_sos_flag                         false
% 2.31/0.98  --inst_sos_phase                        true
% 2.31/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.98  --inst_lit_sel_side                     num_symb
% 2.31/0.98  --inst_solver_per_active                1400
% 2.31/0.98  --inst_solver_calls_frac                1.
% 2.31/0.98  --inst_passive_queue_type               priority_queues
% 2.31/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.98  --inst_passive_queues_freq              [25;2]
% 2.31/0.98  --inst_dismatching                      true
% 2.31/0.98  --inst_eager_unprocessed_to_passive     true
% 2.31/0.98  --inst_prop_sim_given                   true
% 2.31/0.98  --inst_prop_sim_new                     false
% 2.31/0.98  --inst_subs_new                         false
% 2.31/0.98  --inst_eq_res_simp                      false
% 2.31/0.98  --inst_subs_given                       false
% 2.31/0.98  --inst_orphan_elimination               true
% 2.31/0.98  --inst_learning_loop_flag               true
% 2.31/0.98  --inst_learning_start                   3000
% 2.31/0.98  --inst_learning_factor                  2
% 2.31/0.98  --inst_start_prop_sim_after_learn       3
% 2.31/0.98  --inst_sel_renew                        solver
% 2.31/0.98  --inst_lit_activity_flag                true
% 2.31/0.98  --inst_restr_to_given                   false
% 2.31/0.98  --inst_activity_threshold               500
% 2.31/0.98  --inst_out_proof                        true
% 2.31/0.98  
% 2.31/0.98  ------ Resolution Options
% 2.31/0.98  
% 2.31/0.98  --resolution_flag                       true
% 2.31/0.98  --res_lit_sel                           adaptive
% 2.31/0.98  --res_lit_sel_side                      none
% 2.31/0.98  --res_ordering                          kbo
% 2.31/0.98  --res_to_prop_solver                    active
% 2.31/0.98  --res_prop_simpl_new                    false
% 2.31/0.98  --res_prop_simpl_given                  true
% 2.31/0.98  --res_passive_queue_type                priority_queues
% 2.31/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.98  --res_passive_queues_freq               [15;5]
% 2.31/0.98  --res_forward_subs                      full
% 2.31/0.98  --res_backward_subs                     full
% 2.31/0.98  --res_forward_subs_resolution           true
% 2.31/0.98  --res_backward_subs_resolution          true
% 2.31/0.98  --res_orphan_elimination                true
% 2.31/0.98  --res_time_limit                        2.
% 2.31/0.98  --res_out_proof                         true
% 2.31/0.98  
% 2.31/0.98  ------ Superposition Options
% 2.31/0.98  
% 2.31/0.98  --superposition_flag                    true
% 2.31/0.98  --sup_passive_queue_type                priority_queues
% 2.31/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.98  --demod_completeness_check              fast
% 2.31/0.98  --demod_use_ground                      true
% 2.31/0.98  --sup_to_prop_solver                    passive
% 2.31/0.98  --sup_prop_simpl_new                    true
% 2.31/0.98  --sup_prop_simpl_given                  true
% 2.31/0.98  --sup_fun_splitting                     false
% 2.31/0.98  --sup_smt_interval                      50000
% 2.31/0.98  
% 2.31/0.98  ------ Superposition Simplification Setup
% 2.31/0.98  
% 2.31/0.98  --sup_indices_passive                   []
% 2.31/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_full_bw                           [BwDemod]
% 2.31/0.98  --sup_immed_triv                        [TrivRules]
% 2.31/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_immed_bw_main                     []
% 2.31/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.98  
% 2.31/0.98  ------ Combination Options
% 2.31/0.98  
% 2.31/0.98  --comb_res_mult                         3
% 2.31/0.98  --comb_sup_mult                         2
% 2.31/0.98  --comb_inst_mult                        10
% 2.31/0.98  
% 2.31/0.98  ------ Debug Options
% 2.31/0.98  
% 2.31/0.98  --dbg_backtrace                         false
% 2.31/0.98  --dbg_dump_prop_clauses                 false
% 2.31/0.98  --dbg_dump_prop_clauses_file            -
% 2.31/0.98  --dbg_out_stat                          false
% 2.31/0.98  ------ Parsing...
% 2.31/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.31/0.98  ------ Proving...
% 2.31/0.98  ------ Problem Properties 
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  clauses                                 25
% 2.31/0.98  conjectures                             2
% 2.31/0.98  EPR                                     3
% 2.31/0.98  Horn                                    22
% 2.31/0.98  unary                                   10
% 2.31/0.98  binary                                  10
% 2.31/0.98  lits                                    49
% 2.31/0.98  lits eq                                 26
% 2.31/0.98  fd_pure                                 0
% 2.31/0.98  fd_pseudo                               0
% 2.31/0.98  fd_cond                                 5
% 2.31/0.98  fd_pseudo_cond                          1
% 2.31/0.98  AC symbols                              0
% 2.31/0.98  
% 2.31/0.98  ------ Schedule dynamic 5 is on 
% 2.31/0.98  
% 2.31/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.31/0.98  
% 2.31/0.98  
% 2.31/0.98  ------ 
% 2.31/0.98  Current options:
% 2.31/0.98  ------ 
% 2.31/0.98  
% 2.31/0.98  ------ Input Options
% 2.31/0.98  
% 2.31/0.98  --out_options                           all
% 2.31/0.98  --tptp_safe_out                         true
% 2.31/0.98  --problem_path                          ""
% 2.31/0.98  --include_path                          ""
% 2.31/0.98  --clausifier                            res/vclausify_rel
% 2.31/0.98  --clausifier_options                    --mode clausify
% 2.31/0.98  --stdin                                 false
% 2.31/0.98  --stats_out                             all
% 2.31/0.98  
% 2.31/0.98  ------ General Options
% 2.31/0.98  
% 2.31/0.98  --fof                                   false
% 2.31/0.98  --time_out_real                         305.
% 2.31/0.98  --time_out_virtual                      -1.
% 2.31/0.98  --symbol_type_check                     false
% 2.31/0.98  --clausify_out                          false
% 2.31/0.98  --sig_cnt_out                           false
% 2.31/0.98  --trig_cnt_out                          false
% 2.31/0.98  --trig_cnt_out_tolerance                1.
% 2.31/0.98  --trig_cnt_out_sk_spl                   false
% 2.31/0.98  --abstr_cl_out                          false
% 2.31/0.98  
% 2.31/0.98  ------ Global Options
% 2.31/0.98  
% 2.31/0.98  --schedule                              default
% 2.31/0.98  --add_important_lit                     false
% 2.31/0.98  --prop_solver_per_cl                    1000
% 2.31/0.98  --min_unsat_core                        false
% 2.31/0.98  --soft_assumptions                      false
% 2.31/0.98  --soft_lemma_size                       3
% 2.31/0.98  --prop_impl_unit_size                   0
% 2.31/0.98  --prop_impl_unit                        []
% 2.31/0.98  --share_sel_clauses                     true
% 2.31/0.98  --reset_solvers                         false
% 2.31/0.98  --bc_imp_inh                            [conj_cone]
% 2.31/0.98  --conj_cone_tolerance                   3.
% 2.31/0.98  --extra_neg_conj                        none
% 2.31/0.98  --large_theory_mode                     true
% 2.31/0.98  --prolific_symb_bound                   200
% 2.31/0.98  --lt_threshold                          2000
% 2.31/0.98  --clause_weak_htbl                      true
% 2.31/0.98  --gc_record_bc_elim                     false
% 2.31/0.98  
% 2.31/0.98  ------ Preprocessing Options
% 2.31/0.98  
% 2.31/0.98  --preprocessing_flag                    true
% 2.31/0.98  --time_out_prep_mult                    0.1
% 2.31/0.98  --splitting_mode                        input
% 2.31/0.98  --splitting_grd                         true
% 2.31/0.98  --splitting_cvd                         false
% 2.31/0.98  --splitting_cvd_svl                     false
% 2.31/0.98  --splitting_nvd                         32
% 2.31/0.98  --sub_typing                            true
% 2.31/0.98  --prep_gs_sim                           true
% 2.31/0.98  --prep_unflatten                        true
% 2.31/0.98  --prep_res_sim                          true
% 2.31/0.98  --prep_upred                            true
% 2.31/0.98  --prep_sem_filter                       exhaustive
% 2.31/0.98  --prep_sem_filter_out                   false
% 2.31/0.98  --pred_elim                             true
% 2.31/0.98  --res_sim_input                         true
% 2.31/0.98  --eq_ax_congr_red                       true
% 2.31/0.98  --pure_diseq_elim                       true
% 2.31/0.98  --brand_transform                       false
% 2.31/0.98  --non_eq_to_eq                          false
% 2.31/0.98  --prep_def_merge                        true
% 2.31/0.98  --prep_def_merge_prop_impl              false
% 2.31/0.98  --prep_def_merge_mbd                    true
% 2.31/0.98  --prep_def_merge_tr_red                 false
% 2.31/0.98  --prep_def_merge_tr_cl                  false
% 2.31/0.98  --smt_preprocessing                     true
% 2.31/0.98  --smt_ac_axioms                         fast
% 2.31/0.98  --preprocessed_out                      false
% 2.31/0.98  --preprocessed_stats                    false
% 2.31/0.98  
% 2.31/0.98  ------ Abstraction refinement Options
% 2.31/0.98  
% 2.31/0.98  --abstr_ref                             []
% 2.31/0.98  --abstr_ref_prep                        false
% 2.31/0.98  --abstr_ref_until_sat                   false
% 2.31/0.98  --abstr_ref_sig_restrict                funpre
% 2.31/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/0.98  --abstr_ref_under                       []
% 2.31/0.98  
% 2.31/0.98  ------ SAT Options
% 2.31/0.98  
% 2.31/0.98  --sat_mode                              false
% 2.31/0.98  --sat_fm_restart_options                ""
% 2.31/0.98  --sat_gr_def                            false
% 2.31/0.98  --sat_epr_types                         true
% 2.31/0.98  --sat_non_cyclic_types                  false
% 2.31/0.98  --sat_finite_models                     false
% 2.31/0.98  --sat_fm_lemmas                         false
% 2.31/0.98  --sat_fm_prep                           false
% 2.31/0.98  --sat_fm_uc_incr                        true
% 2.31/0.98  --sat_out_model                         small
% 2.31/0.98  --sat_out_clauses                       false
% 2.31/0.98  
% 2.31/0.98  ------ QBF Options
% 2.31/0.98  
% 2.31/0.98  --qbf_mode                              false
% 2.31/0.98  --qbf_elim_univ                         false
% 2.31/0.98  --qbf_dom_inst                          none
% 2.31/0.98  --qbf_dom_pre_inst                      false
% 2.31/0.98  --qbf_sk_in                             false
% 2.31/0.98  --qbf_pred_elim                         true
% 2.31/0.98  --qbf_split                             512
% 2.31/0.98  
% 2.31/0.98  ------ BMC1 Options
% 2.31/0.98  
% 2.31/0.98  --bmc1_incremental                      false
% 2.31/0.98  --bmc1_axioms                           reachable_all
% 2.31/0.98  --bmc1_min_bound                        0
% 2.31/0.98  --bmc1_max_bound                        -1
% 2.31/0.98  --bmc1_max_bound_default                -1
% 2.31/0.98  --bmc1_symbol_reachability              true
% 2.31/0.98  --bmc1_property_lemmas                  false
% 2.31/0.98  --bmc1_k_induction                      false
% 2.31/0.98  --bmc1_non_equiv_states                 false
% 2.31/0.98  --bmc1_deadlock                         false
% 2.31/0.98  --bmc1_ucm                              false
% 2.31/0.98  --bmc1_add_unsat_core                   none
% 2.31/0.98  --bmc1_unsat_core_children              false
% 2.31/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/0.98  --bmc1_out_stat                         full
% 2.31/0.98  --bmc1_ground_init                      false
% 2.31/0.98  --bmc1_pre_inst_next_state              false
% 2.31/0.98  --bmc1_pre_inst_state                   false
% 2.31/0.98  --bmc1_pre_inst_reach_state             false
% 2.31/0.98  --bmc1_out_unsat_core                   false
% 2.31/0.98  --bmc1_aig_witness_out                  false
% 2.31/0.98  --bmc1_verbose                          false
% 2.31/0.98  --bmc1_dump_clauses_tptp                false
% 2.31/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.31/0.98  --bmc1_dump_file                        -
% 2.31/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.31/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.31/0.98  --bmc1_ucm_extend_mode                  1
% 2.31/0.99  --bmc1_ucm_init_mode                    2
% 2.31/0.99  --bmc1_ucm_cone_mode                    none
% 2.31/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.31/0.99  --bmc1_ucm_relax_model                  4
% 2.31/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.31/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/0.99  --bmc1_ucm_layered_model                none
% 2.31/0.99  --bmc1_ucm_max_lemma_size               10
% 2.31/0.99  
% 2.31/0.99  ------ AIG Options
% 2.31/0.99  
% 2.31/0.99  --aig_mode                              false
% 2.31/0.99  
% 2.31/0.99  ------ Instantiation Options
% 2.31/0.99  
% 2.31/0.99  --instantiation_flag                    true
% 2.31/0.99  --inst_sos_flag                         false
% 2.31/0.99  --inst_sos_phase                        true
% 2.31/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/0.99  --inst_lit_sel_side                     none
% 2.31/0.99  --inst_solver_per_active                1400
% 2.31/0.99  --inst_solver_calls_frac                1.
% 2.31/0.99  --inst_passive_queue_type               priority_queues
% 2.31/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/0.99  --inst_passive_queues_freq              [25;2]
% 2.31/0.99  --inst_dismatching                      true
% 2.31/0.99  --inst_eager_unprocessed_to_passive     true
% 2.31/0.99  --inst_prop_sim_given                   true
% 2.31/0.99  --inst_prop_sim_new                     false
% 2.31/0.99  --inst_subs_new                         false
% 2.31/0.99  --inst_eq_res_simp                      false
% 2.31/0.99  --inst_subs_given                       false
% 2.31/0.99  --inst_orphan_elimination               true
% 2.31/0.99  --inst_learning_loop_flag               true
% 2.31/0.99  --inst_learning_start                   3000
% 2.31/0.99  --inst_learning_factor                  2
% 2.31/0.99  --inst_start_prop_sim_after_learn       3
% 2.31/0.99  --inst_sel_renew                        solver
% 2.31/0.99  --inst_lit_activity_flag                true
% 2.31/0.99  --inst_restr_to_given                   false
% 2.31/0.99  --inst_activity_threshold               500
% 2.31/0.99  --inst_out_proof                        true
% 2.31/0.99  
% 2.31/0.99  ------ Resolution Options
% 2.31/0.99  
% 2.31/0.99  --resolution_flag                       false
% 2.31/0.99  --res_lit_sel                           adaptive
% 2.31/0.99  --res_lit_sel_side                      none
% 2.31/0.99  --res_ordering                          kbo
% 2.31/0.99  --res_to_prop_solver                    active
% 2.31/0.99  --res_prop_simpl_new                    false
% 2.31/0.99  --res_prop_simpl_given                  true
% 2.31/0.99  --res_passive_queue_type                priority_queues
% 2.31/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/0.99  --res_passive_queues_freq               [15;5]
% 2.31/0.99  --res_forward_subs                      full
% 2.31/0.99  --res_backward_subs                     full
% 2.31/0.99  --res_forward_subs_resolution           true
% 2.31/0.99  --res_backward_subs_resolution          true
% 2.31/0.99  --res_orphan_elimination                true
% 2.31/0.99  --res_time_limit                        2.
% 2.31/0.99  --res_out_proof                         true
% 2.31/0.99  
% 2.31/0.99  ------ Superposition Options
% 2.31/0.99  
% 2.31/0.99  --superposition_flag                    true
% 2.31/0.99  --sup_passive_queue_type                priority_queues
% 2.31/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.31/0.99  --demod_completeness_check              fast
% 2.31/0.99  --demod_use_ground                      true
% 2.31/0.99  --sup_to_prop_solver                    passive
% 2.31/0.99  --sup_prop_simpl_new                    true
% 2.31/0.99  --sup_prop_simpl_given                  true
% 2.31/0.99  --sup_fun_splitting                     false
% 2.31/0.99  --sup_smt_interval                      50000
% 2.31/0.99  
% 2.31/0.99  ------ Superposition Simplification Setup
% 2.31/0.99  
% 2.31/0.99  --sup_indices_passive                   []
% 2.31/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_full_bw                           [BwDemod]
% 2.31/0.99  --sup_immed_triv                        [TrivRules]
% 2.31/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_immed_bw_main                     []
% 2.31/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/0.99  
% 2.31/0.99  ------ Combination Options
% 2.31/0.99  
% 2.31/0.99  --comb_res_mult                         3
% 2.31/0.99  --comb_sup_mult                         2
% 2.31/0.99  --comb_inst_mult                        10
% 2.31/0.99  
% 2.31/0.99  ------ Debug Options
% 2.31/0.99  
% 2.31/0.99  --dbg_backtrace                         false
% 2.31/0.99  --dbg_dump_prop_clauses                 false
% 2.31/0.99  --dbg_dump_prop_clauses_file            -
% 2.31/0.99  --dbg_out_stat                          false
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  ------ Proving...
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  % SZS status Theorem for theBenchmark.p
% 2.31/0.99  
% 2.31/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.31/0.99  
% 2.31/0.99  fof(f4,axiom,(
% 2.31/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f29,plain,(
% 2.31/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.31/0.99    inference(nnf_transformation,[],[f4])).
% 2.31/0.99  
% 2.31/0.99  fof(f45,plain,(
% 2.31/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f29])).
% 2.31/0.99  
% 2.31/0.99  fof(f10,axiom,(
% 2.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f21,plain,(
% 2.31/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.99    inference(ennf_transformation,[],[f10])).
% 2.31/0.99  
% 2.31/0.99  fof(f22,plain,(
% 2.31/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.99    inference(flattening,[],[f21])).
% 2.31/0.99  
% 2.31/0.99  fof(f32,plain,(
% 2.31/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.99    inference(nnf_transformation,[],[f22])).
% 2.31/0.99  
% 2.31/0.99  fof(f56,plain,(
% 2.31/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/0.99    inference(cnf_transformation,[],[f32])).
% 2.31/0.99  
% 2.31/0.99  fof(f12,conjecture,(
% 2.31/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f13,negated_conjecture,(
% 2.31/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.31/0.99    inference(negated_conjecture,[],[f12])).
% 2.31/0.99  
% 2.31/0.99  fof(f23,plain,(
% 2.31/0.99    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.31/0.99    inference(ennf_transformation,[],[f13])).
% 2.31/0.99  
% 2.31/0.99  fof(f24,plain,(
% 2.31/0.99    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.31/0.99    inference(flattening,[],[f23])).
% 2.31/0.99  
% 2.31/0.99  fof(f35,plain,(
% 2.31/0.99    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) & r1_tarski(k2_relat_1(sK3),sK2) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 2.31/0.99    introduced(choice_axiom,[])).
% 2.31/0.99  
% 2.31/0.99  fof(f36,plain,(
% 2.31/0.99    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)) & r1_tarski(k2_relat_1(sK3),sK2) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 2.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f35])).
% 2.31/0.99  
% 2.31/0.99  fof(f67,plain,(
% 2.31/0.99    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK2) | ~v1_funct_1(sK3)),
% 2.31/0.99    inference(cnf_transformation,[],[f36])).
% 2.31/0.99  
% 2.31/0.99  fof(f65,plain,(
% 2.31/0.99    v1_funct_1(sK3)),
% 2.31/0.99    inference(cnf_transformation,[],[f36])).
% 2.31/0.99  
% 2.31/0.99  fof(f7,axiom,(
% 2.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f17,plain,(
% 2.31/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.99    inference(ennf_transformation,[],[f7])).
% 2.31/0.99  
% 2.31/0.99  fof(f49,plain,(
% 2.31/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/0.99    inference(cnf_transformation,[],[f17])).
% 2.31/0.99  
% 2.31/0.99  fof(f64,plain,(
% 2.31/0.99    v1_relat_1(sK3)),
% 2.31/0.99    inference(cnf_transformation,[],[f36])).
% 2.31/0.99  
% 2.31/0.99  fof(f66,plain,(
% 2.31/0.99    r1_tarski(k2_relat_1(sK3),sK2)),
% 2.31/0.99    inference(cnf_transformation,[],[f36])).
% 2.31/0.99  
% 2.31/0.99  fof(f2,axiom,(
% 2.31/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f25,plain,(
% 2.31/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.31/0.99    inference(nnf_transformation,[],[f2])).
% 2.31/0.99  
% 2.31/0.99  fof(f26,plain,(
% 2.31/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.31/0.99    inference(flattening,[],[f25])).
% 2.31/0.99  
% 2.31/0.99  fof(f38,plain,(
% 2.31/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.31/0.99    inference(cnf_transformation,[],[f26])).
% 2.31/0.99  
% 2.31/0.99  fof(f69,plain,(
% 2.31/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.31/0.99    inference(equality_resolution,[],[f38])).
% 2.31/0.99  
% 2.31/0.99  fof(f8,axiom,(
% 2.31/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f18,plain,(
% 2.31/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.31/0.99    inference(ennf_transformation,[],[f8])).
% 2.31/0.99  
% 2.31/0.99  fof(f19,plain,(
% 2.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.31/0.99    inference(flattening,[],[f18])).
% 2.31/0.99  
% 2.31/0.99  fof(f50,plain,(
% 2.31/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f19])).
% 2.31/0.99  
% 2.31/0.99  fof(f1,axiom,(
% 2.31/0.99    v1_xboole_0(k1_xboole_0)),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f37,plain,(
% 2.31/0.99    v1_xboole_0(k1_xboole_0)),
% 2.31/0.99    inference(cnf_transformation,[],[f1])).
% 2.31/0.99  
% 2.31/0.99  fof(f5,axiom,(
% 2.31/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f16,plain,(
% 2.31/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.31/0.99    inference(ennf_transformation,[],[f5])).
% 2.31/0.99  
% 2.31/0.99  fof(f46,plain,(
% 2.31/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f16])).
% 2.31/0.99  
% 2.31/0.99  fof(f9,axiom,(
% 2.31/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f20,plain,(
% 2.31/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.31/0.99    inference(ennf_transformation,[],[f9])).
% 2.31/0.99  
% 2.31/0.99  fof(f30,plain,(
% 2.31/0.99    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 2.31/0.99    introduced(choice_axiom,[])).
% 2.31/0.99  
% 2.31/0.99  fof(f31,plain,(
% 2.31/0.99    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 2.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f30])).
% 2.31/0.99  
% 2.31/0.99  fof(f51,plain,(
% 2.31/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.31/0.99    inference(cnf_transformation,[],[f31])).
% 2.31/0.99  
% 2.31/0.99  fof(f3,axiom,(
% 2.31/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f27,plain,(
% 2.31/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.31/0.99    inference(nnf_transformation,[],[f3])).
% 2.31/0.99  
% 2.31/0.99  fof(f28,plain,(
% 2.31/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.31/0.99    inference(flattening,[],[f27])).
% 2.31/0.99  
% 2.31/0.99  fof(f43,plain,(
% 2.31/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.31/0.99    inference(cnf_transformation,[],[f28])).
% 2.31/0.99  
% 2.31/0.99  fof(f70,plain,(
% 2.31/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.31/0.99    inference(equality_resolution,[],[f43])).
% 2.31/0.99  
% 2.31/0.99  fof(f42,plain,(
% 2.31/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.31/0.99    inference(cnf_transformation,[],[f28])).
% 2.31/0.99  
% 2.31/0.99  fof(f71,plain,(
% 2.31/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.31/0.99    inference(equality_resolution,[],[f42])).
% 2.31/0.99  
% 2.31/0.99  fof(f11,axiom,(
% 2.31/0.99    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.31/0.99  
% 2.31/0.99  fof(f14,plain,(
% 2.31/0.99    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.31/0.99  
% 2.31/0.99  fof(f15,plain,(
% 2.31/0.99    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.31/0.99  
% 2.31/0.99  fof(f33,plain,(
% 2.31/0.99    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK1(X0,X1),X0,X1) & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.31/0.99    introduced(choice_axiom,[])).
% 2.31/0.99  
% 2.31/0.99  fof(f34,plain,(
% 2.31/0.99    ! [X0,X1] : (v1_funct_2(sK1(X0,X1),X0,X1) & v1_funct_1(sK1(X0,X1)) & v1_relat_1(sK1(X0,X1)) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f33])).
% 2.31/0.99  
% 2.31/0.99  fof(f63,plain,(
% 2.31/0.99    ( ! [X0,X1] : (v1_funct_2(sK1(X0,X1),X0,X1)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f34])).
% 2.31/0.99  
% 2.31/0.99  fof(f60,plain,(
% 2.31/0.99    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/0.99    inference(cnf_transformation,[],[f34])).
% 2.31/0.99  
% 2.31/0.99  fof(f59,plain,(
% 2.31/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/0.99    inference(cnf_transformation,[],[f32])).
% 2.31/0.99  
% 2.31/0.99  fof(f72,plain,(
% 2.31/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/0.99    inference(equality_resolution,[],[f59])).
% 2.31/0.99  
% 2.31/0.99  fof(f73,plain,(
% 2.31/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.31/0.99    inference(equality_resolution,[],[f72])).
% 2.31/0.99  
% 2.31/0.99  fof(f41,plain,(
% 2.31/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.31/0.99    inference(cnf_transformation,[],[f28])).
% 2.31/0.99  
% 2.31/0.99  cnf(c_7,plain,
% 2.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1191,plain,
% 2.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.31/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_20,plain,
% 2.31/0.99      ( v1_funct_2(X0,X1,X2)
% 2.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.31/0.99      | k1_xboole_0 = X2 ),
% 2.31/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_27,negated_conjecture,
% 2.31/0.99      ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
% 2.31/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | ~ v1_funct_1(sK3) ),
% 2.31/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_29,negated_conjecture,
% 2.31/0.99      ( v1_funct_1(sK3) ),
% 2.31/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_153,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2) ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_27,c_29]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_154,negated_conjecture,
% 2.31/0.99      ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK2)
% 2.31/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
% 2.31/0.99      inference(renaming,[status(thm)],[c_153]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_528,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | k1_relset_1(X1,X2,X0) != X1
% 2.31/0.99      | k1_relat_1(sK3) != X1
% 2.31/0.99      | sK2 != X2
% 2.31/0.99      | sK3 != X0
% 2.31/0.99      | k1_xboole_0 = X2 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_154]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_529,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | k1_relset_1(k1_relat_1(sK3),sK2,sK3) != k1_relat_1(sK3)
% 2.31/0.99      | k1_xboole_0 = sK2 ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_528]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_12,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.31/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_537,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | k1_xboole_0 = sK2 ),
% 2.31/0.99      inference(forward_subsumption_resolution,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_529,c_12]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1180,plain,
% 2.31/0.99      ( k1_xboole_0 = sK2
% 2.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2066,plain,
% 2.31/0.99      ( sK2 = k1_xboole_0
% 2.31/0.99      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK2)) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_1191,c_1180]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_30,negated_conjecture,
% 2.31/0.99      ( v1_relat_1(sK3) ),
% 2.31/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_28,negated_conjecture,
% 2.31/0.99      ( r1_tarski(k2_relat_1(sK3),sK2) ),
% 2.31/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3,plain,
% 2.31/0.99      ( r1_tarski(X0,X0) ),
% 2.31/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1417,plain,
% 2.31/0.99      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_762,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1372,plain,
% 2.31/0.99      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_762]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1452,plain,
% 2.31/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1372]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_761,plain,( X0 = X0 ),theory(equality) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1453,plain,
% 2.31/0.99      ( sK2 = sK2 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_761]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_13,plain,
% 2.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.31/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.31/0.99      | ~ v1_relat_1(X0) ),
% 2.31/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1369,plain,
% 2.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.31/0.99      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.31/0.99      | ~ r1_tarski(k2_relat_1(sK3),X1)
% 2.31/0.99      | ~ v1_relat_1(sK3) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1416,plain,
% 2.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
% 2.31/0.99      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 2.31/0.99      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.31/0.99      | ~ v1_relat_1(sK3) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1369]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1519,plain,
% 2.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3))
% 2.31/0.99      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.31/0.99      | ~ v1_relat_1(sK3) ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1416]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2150,plain,
% 2.31/0.99      ( sK2 = k1_xboole_0 ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_2066,c_30,c_28,c_537,c_1417,c_1452,c_1453,c_1519]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1185,plain,
% 2.31/0.99      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2157,plain,
% 2.31/0.99      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 2.31/0.99      inference(demodulation,[status(thm)],[c_2150,c_1185]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_0,plain,
% 2.31/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.31/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_9,plain,
% 2.31/0.99      ( ~ r2_hidden(X0,X1)
% 2.31/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.31/0.99      | ~ v1_xboole_0(X2) ),
% 2.31/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_353,plain,
% 2.31/0.99      ( ~ r2_hidden(X0,X1)
% 2.31/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.31/0.99      | k1_xboole_0 != X2 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_354,plain,
% 2.31/0.99      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_16,plain,
% 2.31/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.31/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_402,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 2.31/0.99      | X1 != X0
% 2.31/0.99      | sK0(X1) != X2
% 2.31/0.99      | k1_xboole_0 = X1 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_354,c_16]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_403,plain,
% 2.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_402]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1183,plain,
% 2.31/0.99      ( k1_xboole_0 = X0
% 2.31/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2067,plain,
% 2.31/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_1191,c_1183]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2598,plain,
% 2.31/0.99      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_2157,c_2067]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1192,plain,
% 2.31/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_4,plain,
% 2.31/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.31/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1188,plain,
% 2.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.31/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.31/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 2.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1983,plain,
% 2.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.31/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.31/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 2.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_4,c_1188]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2964,plain,
% 2.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.31/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 2.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_1192,c_1983]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3375,plain,
% 2.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.31/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.31/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_2598,c_2964]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_5,plain,
% 2.31/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.31/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1984,plain,
% 2.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.31/0.99      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 2.31/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_5,c_1188]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2986,plain,
% 2.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.31/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.31/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.31/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_2598,c_1984]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_31,plain,
% 2.31/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_89,plain,
% 2.31/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_91,plain,
% 2.31/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_89]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1679,plain,
% 2.31/0.99      ( sK3 = sK3 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_761]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_23,plain,
% 2.31/0.99      ( v1_funct_2(sK1(X0,X1),X0,X1) ),
% 2.31/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_541,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | sK1(X0,X1) != sK3
% 2.31/0.99      | k1_relat_1(sK3) != X0
% 2.31/0.99      | sK2 != X1 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_154]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_542,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | sK1(k1_relat_1(sK3),sK2) != sK3 ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_541]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1179,plain,
% 2.31/0.99      ( sK1(k1_relat_1(sK3),sK2) != sK3
% 2.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2156,plain,
% 2.31/0.99      ( sK1(k1_relat_1(sK3),k1_xboole_0) != sK3
% 2.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
% 2.31/0.99      inference(demodulation,[status(thm)],[c_2150,c_1179]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_26,plain,
% 2.31/0.99      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.31/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1186,plain,
% 2.31/0.99      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1807,plain,
% 2.31/0.99      ( m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_4,c_1186]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1907,plain,
% 2.31/0.99      ( sK1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.31/0.99      inference(superposition,[status(thm)],[c_1807,c_1183]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2162,plain,
% 2.31/0.99      ( sK3 != k1_xboole_0
% 2.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.31/0.99      inference(demodulation,[status(thm)],[c_2156,c_4,c_1907]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1649,plain,
% 2.31/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_762]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2270,plain,
% 2.31/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1649]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2271,plain,
% 2.31/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_2270]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2935,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK3 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_403]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_2936,plain,
% 2.31/0.99      ( k1_xboole_0 = sK3
% 2.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2935]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3136,plain,
% 2.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.31/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.31/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.31/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_2986]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_3238,plain,
% 2.31/0.99      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_2986,c_31,c_91,c_1679,c_2162,c_2271,c_2936,c_3136]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_763,plain,
% 2.31/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.31/0.99      theory(equality) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1424,plain,
% 2.31/0.99      ( ~ r1_tarski(X0,X1)
% 2.31/0.99      | r1_tarski(k1_relat_1(sK3),X2)
% 2.31/0.99      | X2 != X1
% 2.31/0.99      | k1_relat_1(sK3) != X0 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_763]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1425,plain,
% 2.31/0.99      ( X0 != X1
% 2.31/0.99      | k1_relat_1(sK3) != X2
% 2.31/0.99      | r1_tarski(X2,X1) != iProver_top
% 2.31/0.99      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1424]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1427,plain,
% 2.31/0.99      ( k1_relat_1(sK3) != k1_xboole_0
% 2.31/0.99      | k1_xboole_0 != k1_xboole_0
% 2.31/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
% 2.31/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_1425]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_17,plain,
% 2.31/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 2.31/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.31/0.99      | k1_xboole_0 = X0 ),
% 2.31/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_447,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 2.31/0.99      | k1_relat_1(sK3) != X0
% 2.31/0.99      | sK2 != k1_xboole_0
% 2.31/0.99      | sK3 != k1_xboole_0
% 2.31/0.99      | k1_xboole_0 = X0 ),
% 2.31/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_154]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_448,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
% 2.31/0.99      | sK2 != k1_xboole_0
% 2.31/0.99      | sK3 != k1_xboole_0
% 2.31/0.99      | k1_xboole_0 = k1_relat_1(sK3) ),
% 2.31/0.99      inference(unflattening,[status(thm)],[c_447]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1182,plain,
% 2.31/0.99      ( sK2 != k1_xboole_0
% 2.31/0.99      | sK3 != k1_xboole_0
% 2.31/0.99      | k1_xboole_0 = k1_relat_1(sK3)
% 2.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 2.31/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0))) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1283,plain,
% 2.31/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 2.31/0.99      | sK2 != k1_xboole_0
% 2.31/0.99      | sK3 != k1_xboole_0
% 2.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 2.31/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.31/0.99      inference(demodulation,[status(thm)],[c_1182,c_4]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_84,plain,
% 2.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.31/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.31/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_86,plain,
% 2.31/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 2.31/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_84]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1386,plain,
% 2.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top
% 2.31/0.99      | sK3 != k1_xboole_0
% 2.31/0.99      | sK2 != k1_xboole_0
% 2.31/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.31/0.99      inference(global_propositional_subsumption,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_1283,c_86,c_91]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1387,plain,
% 2.31/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 2.31/0.99      | sK2 != k1_xboole_0
% 2.31/0.99      | sK3 != k1_xboole_0
% 2.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
% 2.31/0.99      inference(renaming,[status(thm)],[c_1386]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_1388,plain,
% 2.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
% 2.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 2.31/0.99      | sK2 != k1_xboole_0
% 2.31/0.99      | sK3 != k1_xboole_0 ),
% 2.31/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1387]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_88,plain,
% 2.31/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_6,plain,
% 2.31/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.31/0.99      | k1_xboole_0 = X1
% 2.31/0.99      | k1_xboole_0 = X0 ),
% 2.31/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(c_87,plain,
% 2.31/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.31/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.31/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.31/0.99  
% 2.31/0.99  cnf(contradiction,plain,
% 2.31/0.99      ( $false ),
% 2.31/0.99      inference(minisat,
% 2.31/0.99                [status(thm)],
% 2.31/0.99                [c_3375,c_3238,c_2936,c_2271,c_1679,c_1519,c_1453,c_1452,
% 2.31/0.99                 c_1427,c_1417,c_1388,c_537,c_91,c_88,c_87,c_28,c_31,
% 2.31/0.99                 c_30]) ).
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.31/0.99  
% 2.31/0.99  ------                               Statistics
% 2.31/0.99  
% 2.31/0.99  ------ General
% 2.31/0.99  
% 2.31/0.99  abstr_ref_over_cycles:                  0
% 2.31/0.99  abstr_ref_under_cycles:                 0
% 2.31/0.99  gc_basic_clause_elim:                   0
% 2.31/0.99  forced_gc_time:                         0
% 2.31/0.99  parsing_time:                           0.014
% 2.31/0.99  unif_index_cands_time:                  0.
% 2.31/0.99  unif_index_add_time:                    0.
% 2.31/0.99  orderings_time:                         0.
% 2.31/0.99  out_proof_time:                         0.01
% 2.31/0.99  total_time:                             0.127
% 2.31/0.99  num_of_symbols:                         49
% 2.31/0.99  num_of_terms:                           2678
% 2.31/0.99  
% 2.31/0.99  ------ Preprocessing
% 2.31/0.99  
% 2.31/0.99  num_of_splits:                          0
% 2.31/0.99  num_of_split_atoms:                     0
% 2.31/0.99  num_of_reused_defs:                     0
% 2.31/0.99  num_eq_ax_congr_red:                    16
% 2.31/0.99  num_of_sem_filtered_clauses:            3
% 2.31/0.99  num_of_subtypes:                        0
% 2.31/0.99  monotx_restored_types:                  0
% 2.31/0.99  sat_num_of_epr_types:                   0
% 2.31/0.99  sat_num_of_non_cyclic_types:            0
% 2.31/0.99  sat_guarded_non_collapsed_types:        0
% 2.31/0.99  num_pure_diseq_elim:                    0
% 2.31/0.99  simp_replaced_by:                       0
% 2.31/0.99  res_preprocessed:                       130
% 2.31/0.99  prep_upred:                             0
% 2.31/0.99  prep_unflattend:                        48
% 2.31/0.99  smt_new_axioms:                         0
% 2.31/0.99  pred_elim_cands:                        3
% 2.31/0.99  pred_elim:                              3
% 2.31/0.99  pred_elim_cl:                           3
% 2.31/0.99  pred_elim_cycles:                       6
% 2.31/0.99  merged_defs:                            8
% 2.31/0.99  merged_defs_ncl:                        0
% 2.31/0.99  bin_hyper_res:                          8
% 2.31/0.99  prep_cycles:                            4
% 2.31/0.99  pred_elim_time:                         0.006
% 2.31/0.99  splitting_time:                         0.
% 2.31/0.99  sem_filter_time:                        0.
% 2.31/0.99  monotx_time:                            0.
% 2.31/0.99  subtype_inf_time:                       0.
% 2.31/0.99  
% 2.31/0.99  ------ Problem properties
% 2.31/0.99  
% 2.31/0.99  clauses:                                25
% 2.31/0.99  conjectures:                            2
% 2.31/0.99  epr:                                    3
% 2.31/0.99  horn:                                   22
% 2.31/0.99  ground:                                 8
% 2.31/0.99  unary:                                  10
% 2.31/0.99  binary:                                 10
% 2.31/0.99  lits:                                   49
% 2.31/0.99  lits_eq:                                26
% 2.31/0.99  fd_pure:                                0
% 2.31/0.99  fd_pseudo:                              0
% 2.31/0.99  fd_cond:                                5
% 2.31/0.99  fd_pseudo_cond:                         1
% 2.31/0.99  ac_symbols:                             0
% 2.31/0.99  
% 2.31/0.99  ------ Propositional Solver
% 2.31/0.99  
% 2.31/0.99  prop_solver_calls:                      26
% 2.31/0.99  prop_fast_solver_calls:                 711
% 2.31/0.99  smt_solver_calls:                       0
% 2.31/0.99  smt_fast_solver_calls:                  0
% 2.31/0.99  prop_num_of_clauses:                    1030
% 2.31/0.99  prop_preprocess_simplified:             4167
% 2.31/0.99  prop_fo_subsumed:                       7
% 2.31/0.99  prop_solver_time:                       0.
% 2.31/0.99  smt_solver_time:                        0.
% 2.31/0.99  smt_fast_solver_time:                   0.
% 2.31/0.99  prop_fast_solver_time:                  0.
% 2.31/0.99  prop_unsat_core_time:                   0.
% 2.31/0.99  
% 2.31/0.99  ------ QBF
% 2.31/0.99  
% 2.31/0.99  qbf_q_res:                              0
% 2.31/0.99  qbf_num_tautologies:                    0
% 2.31/0.99  qbf_prep_cycles:                        0
% 2.31/0.99  
% 2.31/0.99  ------ BMC1
% 2.31/0.99  
% 2.31/0.99  bmc1_current_bound:                     -1
% 2.31/0.99  bmc1_last_solved_bound:                 -1
% 2.31/0.99  bmc1_unsat_core_size:                   -1
% 2.31/0.99  bmc1_unsat_core_parents_size:           -1
% 2.31/0.99  bmc1_merge_next_fun:                    0
% 2.31/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.31/0.99  
% 2.31/0.99  ------ Instantiation
% 2.31/0.99  
% 2.31/0.99  inst_num_of_clauses:                    326
% 2.31/0.99  inst_num_in_passive:                    55
% 2.31/0.99  inst_num_in_active:                     192
% 2.31/0.99  inst_num_in_unprocessed:                79
% 2.31/0.99  inst_num_of_loops:                      260
% 2.31/0.99  inst_num_of_learning_restarts:          0
% 2.31/0.99  inst_num_moves_active_passive:          66
% 2.31/0.99  inst_lit_activity:                      0
% 2.31/0.99  inst_lit_activity_moves:                0
% 2.31/0.99  inst_num_tautologies:                   0
% 2.31/0.99  inst_num_prop_implied:                  0
% 2.31/0.99  inst_num_existing_simplified:           0
% 2.31/0.99  inst_num_eq_res_simplified:             0
% 2.31/0.99  inst_num_child_elim:                    0
% 2.31/0.99  inst_num_of_dismatching_blockings:      63
% 2.31/0.99  inst_num_of_non_proper_insts:           316
% 2.31/0.99  inst_num_of_duplicates:                 0
% 2.31/0.99  inst_inst_num_from_inst_to_res:         0
% 2.31/0.99  inst_dismatching_checking_time:         0.
% 2.31/0.99  
% 2.31/0.99  ------ Resolution
% 2.31/0.99  
% 2.31/0.99  res_num_of_clauses:                     0
% 2.31/0.99  res_num_in_passive:                     0
% 2.31/0.99  res_num_in_active:                      0
% 2.31/0.99  res_num_of_loops:                       134
% 2.31/0.99  res_forward_subset_subsumed:            24
% 2.31/0.99  res_backward_subset_subsumed:           0
% 2.31/0.99  res_forward_subsumed:                   0
% 2.31/0.99  res_backward_subsumed:                  0
% 2.31/0.99  res_forward_subsumption_resolution:     3
% 2.31/0.99  res_backward_subsumption_resolution:    0
% 2.31/0.99  res_clause_to_clause_subsumption:       228
% 2.31/0.99  res_orphan_elimination:                 0
% 2.31/0.99  res_tautology_del:                      43
% 2.31/0.99  res_num_eq_res_simplified:              0
% 2.31/0.99  res_num_sel_changes:                    0
% 2.31/0.99  res_moves_from_active_to_pass:          0
% 2.31/0.99  
% 2.31/0.99  ------ Superposition
% 2.31/0.99  
% 2.31/0.99  sup_time_total:                         0.
% 2.31/0.99  sup_time_generating:                    0.
% 2.31/0.99  sup_time_sim_full:                      0.
% 2.31/0.99  sup_time_sim_immed:                     0.
% 2.31/0.99  
% 2.31/0.99  sup_num_of_clauses:                     47
% 2.31/0.99  sup_num_in_active:                      40
% 2.31/0.99  sup_num_in_passive:                     7
% 2.31/0.99  sup_num_of_loops:                       51
% 2.31/0.99  sup_fw_superposition:                   48
% 2.31/0.99  sup_bw_superposition:                   13
% 2.31/0.99  sup_immediate_simplified:               24
% 2.31/0.99  sup_given_eliminated:                   2
% 2.31/0.99  comparisons_done:                       0
% 2.31/0.99  comparisons_avoided:                    0
% 2.31/0.99  
% 2.31/0.99  ------ Simplifications
% 2.31/0.99  
% 2.31/0.99  
% 2.31/0.99  sim_fw_subset_subsumed:                 6
% 2.31/0.99  sim_bw_subset_subsumed:                 2
% 2.31/0.99  sim_fw_subsumed:                        1
% 2.31/0.99  sim_bw_subsumed:                        3
% 2.31/0.99  sim_fw_subsumption_res:                 0
% 2.31/0.99  sim_bw_subsumption_res:                 0
% 2.31/0.99  sim_tautology_del:                      1
% 2.31/0.99  sim_eq_tautology_del:                   14
% 2.31/0.99  sim_eq_res_simp:                        1
% 2.31/0.99  sim_fw_demodulated:                     6
% 2.31/0.99  sim_bw_demodulated:                     9
% 2.31/0.99  sim_light_normalised:                   16
% 2.31/0.99  sim_joinable_taut:                      0
% 2.31/0.99  sim_joinable_simp:                      0
% 2.31/0.99  sim_ac_normalised:                      0
% 2.31/0.99  sim_smt_subsumption:                    0
% 2.31/0.99  
%------------------------------------------------------------------------------
