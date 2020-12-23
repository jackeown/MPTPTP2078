%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:24 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 408 expanded)
%              Number of clauses        :   55 ( 104 expanded)
%              Number of leaves         :   16 (  95 expanded)
%              Depth                    :   20
%              Number of atoms          :  374 (1182 expanded)
%              Number of equality atoms :  234 ( 637 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f35])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f63,f68])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f34,plain,(
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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f86,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f87,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f66,f68,f68])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_302,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_303,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_1482,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_2051,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1482])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2240,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2241,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2240])).

cnf(c_2554,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2051,c_2241])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1484,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2560,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2554,c_1484])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1485,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2559,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2554,c_1485])).

cnf(c_3923,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2560,c_2559])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_362,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_363,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1654,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_363])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_317,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_318,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_480,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_318])).

cnf(c_481,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_482,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_23])).

cnf(c_483,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_844,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_483])).

cnf(c_1958,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1654,c_844])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1487,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2561,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2554,c_1487])).

cnf(c_4470,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_1958,c_2561])).

cnf(c_8303,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3923,c_4470])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1489,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2199,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1958,c_1489])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_283,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_1483,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_2707,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2199,c_1483])).

cnf(c_2710,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2707,c_2051,c_2241])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_353,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_354,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1651,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_354])).

cnf(c_22,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1744,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1651,c_22])).

cnf(c_2713,plain,
    ( k11_relat_1(sK3,sK1) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2710,c_1744])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8303,c_2713])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.02/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.99  
% 3.02/0.99  ------  iProver source info
% 3.02/0.99  
% 3.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.99  git: non_committed_changes: false
% 3.02/0.99  git: last_make_outside_of_git: false
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     num_symb
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       true
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  ------ Parsing...
% 3.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.99  ------ Proving...
% 3.02/0.99  ------ Problem Properties 
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  clauses                                 21
% 3.02/0.99  conjectures                             2
% 3.02/1.00  EPR                                     1
% 3.02/1.00  Horn                                    18
% 3.02/1.00  unary                                   7
% 3.02/1.00  binary                                  5
% 3.02/1.00  lits                                    48
% 3.02/1.00  lits eq                                 32
% 3.02/1.00  fd_pure                                 0
% 3.02/1.00  fd_pseudo                               0
% 3.02/1.00  fd_cond                                 0
% 3.02/1.00  fd_pseudo_cond                          4
% 3.02/1.00  AC symbols                              0
% 3.02/1.00  
% 3.02/1.00  ------ Schedule dynamic 5 is on 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  ------ 
% 3.02/1.00  Current options:
% 3.02/1.00  ------ 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options
% 3.02/1.00  
% 3.02/1.00  --out_options                           all
% 3.02/1.00  --tptp_safe_out                         true
% 3.02/1.00  --problem_path                          ""
% 3.02/1.00  --include_path                          ""
% 3.02/1.00  --clausifier                            res/vclausify_rel
% 3.02/1.00  --clausifier_options                    --mode clausify
% 3.02/1.00  --stdin                                 false
% 3.02/1.00  --stats_out                             all
% 3.02/1.00  
% 3.02/1.00  ------ General Options
% 3.02/1.00  
% 3.02/1.00  --fof                                   false
% 3.02/1.00  --time_out_real                         305.
% 3.02/1.00  --time_out_virtual                      -1.
% 3.02/1.00  --symbol_type_check                     false
% 3.02/1.00  --clausify_out                          false
% 3.02/1.00  --sig_cnt_out                           false
% 3.02/1.00  --trig_cnt_out                          false
% 3.02/1.00  --trig_cnt_out_tolerance                1.
% 3.02/1.00  --trig_cnt_out_sk_spl                   false
% 3.02/1.00  --abstr_cl_out                          false
% 3.02/1.00  
% 3.02/1.00  ------ Global Options
% 3.02/1.00  
% 3.02/1.00  --schedule                              default
% 3.02/1.00  --add_important_lit                     false
% 3.02/1.00  --prop_solver_per_cl                    1000
% 3.02/1.00  --min_unsat_core                        false
% 3.02/1.00  --soft_assumptions                      false
% 3.02/1.00  --soft_lemma_size                       3
% 3.02/1.00  --prop_impl_unit_size                   0
% 3.02/1.00  --prop_impl_unit                        []
% 3.02/1.00  --share_sel_clauses                     true
% 3.02/1.00  --reset_solvers                         false
% 3.02/1.00  --bc_imp_inh                            [conj_cone]
% 3.02/1.00  --conj_cone_tolerance                   3.
% 3.02/1.00  --extra_neg_conj                        none
% 3.02/1.00  --large_theory_mode                     true
% 3.02/1.00  --prolific_symb_bound                   200
% 3.02/1.00  --lt_threshold                          2000
% 3.02/1.00  --clause_weak_htbl                      true
% 3.02/1.00  --gc_record_bc_elim                     false
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing Options
% 3.02/1.00  
% 3.02/1.00  --preprocessing_flag                    true
% 3.02/1.00  --time_out_prep_mult                    0.1
% 3.02/1.00  --splitting_mode                        input
% 3.02/1.00  --splitting_grd                         true
% 3.02/1.00  --splitting_cvd                         false
% 3.02/1.00  --splitting_cvd_svl                     false
% 3.02/1.00  --splitting_nvd                         32
% 3.02/1.00  --sub_typing                            true
% 3.02/1.00  --prep_gs_sim                           true
% 3.02/1.00  --prep_unflatten                        true
% 3.02/1.00  --prep_res_sim                          true
% 3.02/1.00  --prep_upred                            true
% 3.02/1.00  --prep_sem_filter                       exhaustive
% 3.02/1.00  --prep_sem_filter_out                   false
% 3.02/1.00  --pred_elim                             true
% 3.02/1.00  --res_sim_input                         true
% 3.02/1.00  --eq_ax_congr_red                       true
% 3.02/1.00  --pure_diseq_elim                       true
% 3.02/1.00  --brand_transform                       false
% 3.02/1.00  --non_eq_to_eq                          false
% 3.02/1.00  --prep_def_merge                        true
% 3.02/1.00  --prep_def_merge_prop_impl              false
% 3.02/1.00  --prep_def_merge_mbd                    true
% 3.02/1.00  --prep_def_merge_tr_red                 false
% 3.02/1.00  --prep_def_merge_tr_cl                  false
% 3.02/1.00  --smt_preprocessing                     true
% 3.02/1.00  --smt_ac_axioms                         fast
% 3.02/1.00  --preprocessed_out                      false
% 3.02/1.00  --preprocessed_stats                    false
% 3.02/1.00  
% 3.02/1.00  ------ Abstraction refinement Options
% 3.02/1.00  
% 3.02/1.00  --abstr_ref                             []
% 3.02/1.00  --abstr_ref_prep                        false
% 3.02/1.00  --abstr_ref_until_sat                   false
% 3.02/1.00  --abstr_ref_sig_restrict                funpre
% 3.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.00  --abstr_ref_under                       []
% 3.02/1.00  
% 3.02/1.00  ------ SAT Options
% 3.02/1.00  
% 3.02/1.00  --sat_mode                              false
% 3.02/1.00  --sat_fm_restart_options                ""
% 3.02/1.00  --sat_gr_def                            false
% 3.02/1.00  --sat_epr_types                         true
% 3.02/1.00  --sat_non_cyclic_types                  false
% 3.02/1.00  --sat_finite_models                     false
% 3.02/1.00  --sat_fm_lemmas                         false
% 3.02/1.00  --sat_fm_prep                           false
% 3.02/1.00  --sat_fm_uc_incr                        true
% 3.02/1.00  --sat_out_model                         small
% 3.02/1.00  --sat_out_clauses                       false
% 3.02/1.00  
% 3.02/1.00  ------ QBF Options
% 3.02/1.00  
% 3.02/1.00  --qbf_mode                              false
% 3.02/1.00  --qbf_elim_univ                         false
% 3.02/1.00  --qbf_dom_inst                          none
% 3.02/1.00  --qbf_dom_pre_inst                      false
% 3.02/1.00  --qbf_sk_in                             false
% 3.02/1.00  --qbf_pred_elim                         true
% 3.02/1.00  --qbf_split                             512
% 3.02/1.00  
% 3.02/1.00  ------ BMC1 Options
% 3.02/1.00  
% 3.02/1.00  --bmc1_incremental                      false
% 3.02/1.00  --bmc1_axioms                           reachable_all
% 3.02/1.00  --bmc1_min_bound                        0
% 3.02/1.00  --bmc1_max_bound                        -1
% 3.02/1.00  --bmc1_max_bound_default                -1
% 3.02/1.00  --bmc1_symbol_reachability              true
% 3.02/1.00  --bmc1_property_lemmas                  false
% 3.02/1.00  --bmc1_k_induction                      false
% 3.02/1.00  --bmc1_non_equiv_states                 false
% 3.02/1.00  --bmc1_deadlock                         false
% 3.02/1.00  --bmc1_ucm                              false
% 3.02/1.00  --bmc1_add_unsat_core                   none
% 3.02/1.00  --bmc1_unsat_core_children              false
% 3.02/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.00  --bmc1_out_stat                         full
% 3.02/1.00  --bmc1_ground_init                      false
% 3.02/1.00  --bmc1_pre_inst_next_state              false
% 3.02/1.00  --bmc1_pre_inst_state                   false
% 3.02/1.00  --bmc1_pre_inst_reach_state             false
% 3.02/1.00  --bmc1_out_unsat_core                   false
% 3.02/1.00  --bmc1_aig_witness_out                  false
% 3.02/1.00  --bmc1_verbose                          false
% 3.02/1.00  --bmc1_dump_clauses_tptp                false
% 3.02/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.00  --bmc1_dump_file                        -
% 3.02/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.00  --bmc1_ucm_extend_mode                  1
% 3.02/1.00  --bmc1_ucm_init_mode                    2
% 3.02/1.00  --bmc1_ucm_cone_mode                    none
% 3.02/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.00  --bmc1_ucm_relax_model                  4
% 3.02/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.00  --bmc1_ucm_layered_model                none
% 3.02/1.00  --bmc1_ucm_max_lemma_size               10
% 3.02/1.00  
% 3.02/1.00  ------ AIG Options
% 3.02/1.00  
% 3.02/1.00  --aig_mode                              false
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation Options
% 3.02/1.00  
% 3.02/1.00  --instantiation_flag                    true
% 3.02/1.00  --inst_sos_flag                         false
% 3.02/1.00  --inst_sos_phase                        true
% 3.02/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel_side                     none
% 3.02/1.00  --inst_solver_per_active                1400
% 3.02/1.00  --inst_solver_calls_frac                1.
% 3.02/1.00  --inst_passive_queue_type               priority_queues
% 3.02/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.00  --inst_passive_queues_freq              [25;2]
% 3.02/1.00  --inst_dismatching                      true
% 3.02/1.00  --inst_eager_unprocessed_to_passive     true
% 3.02/1.00  --inst_prop_sim_given                   true
% 3.02/1.00  --inst_prop_sim_new                     false
% 3.02/1.00  --inst_subs_new                         false
% 3.02/1.00  --inst_eq_res_simp                      false
% 3.02/1.00  --inst_subs_given                       false
% 3.02/1.00  --inst_orphan_elimination               true
% 3.02/1.00  --inst_learning_loop_flag               true
% 3.02/1.00  --inst_learning_start                   3000
% 3.02/1.00  --inst_learning_factor                  2
% 3.02/1.00  --inst_start_prop_sim_after_learn       3
% 3.02/1.00  --inst_sel_renew                        solver
% 3.02/1.00  --inst_lit_activity_flag                true
% 3.02/1.00  --inst_restr_to_given                   false
% 3.02/1.00  --inst_activity_threshold               500
% 3.02/1.00  --inst_out_proof                        true
% 3.02/1.00  
% 3.02/1.00  ------ Resolution Options
% 3.02/1.00  
% 3.02/1.00  --resolution_flag                       false
% 3.02/1.00  --res_lit_sel                           adaptive
% 3.02/1.00  --res_lit_sel_side                      none
% 3.02/1.00  --res_ordering                          kbo
% 3.02/1.00  --res_to_prop_solver                    active
% 3.02/1.00  --res_prop_simpl_new                    false
% 3.02/1.00  --res_prop_simpl_given                  true
% 3.02/1.00  --res_passive_queue_type                priority_queues
% 3.02/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.00  --res_passive_queues_freq               [15;5]
% 3.02/1.00  --res_forward_subs                      full
% 3.02/1.00  --res_backward_subs                     full
% 3.02/1.00  --res_forward_subs_resolution           true
% 3.02/1.00  --res_backward_subs_resolution          true
% 3.02/1.00  --res_orphan_elimination                true
% 3.02/1.00  --res_time_limit                        2.
% 3.02/1.00  --res_out_proof                         true
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Options
% 3.02/1.00  
% 3.02/1.00  --superposition_flag                    true
% 3.02/1.00  --sup_passive_queue_type                priority_queues
% 3.02/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.00  --demod_completeness_check              fast
% 3.02/1.00  --demod_use_ground                      true
% 3.02/1.00  --sup_to_prop_solver                    passive
% 3.02/1.00  --sup_prop_simpl_new                    true
% 3.02/1.00  --sup_prop_simpl_given                  true
% 3.02/1.00  --sup_fun_splitting                     false
% 3.02/1.00  --sup_smt_interval                      50000
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Simplification Setup
% 3.02/1.00  
% 3.02/1.00  --sup_indices_passive                   []
% 3.02/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_full_bw                           [BwDemod]
% 3.02/1.00  --sup_immed_triv                        [TrivRules]
% 3.02/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_immed_bw_main                     []
% 3.02/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  
% 3.02/1.00  ------ Combination Options
% 3.02/1.00  
% 3.02/1.00  --comb_res_mult                         3
% 3.02/1.00  --comb_sup_mult                         2
% 3.02/1.00  --comb_inst_mult                        10
% 3.02/1.00  
% 3.02/1.00  ------ Debug Options
% 3.02/1.00  
% 3.02/1.00  --dbg_backtrace                         false
% 3.02/1.00  --dbg_dump_prop_clauses                 false
% 3.02/1.00  --dbg_dump_prop_clauses_file            -
% 3.02/1.00  --dbg_out_stat                          false
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  ------ Proving...
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  % SZS status Theorem for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  fof(f5,axiom,(
% 3.02/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f17,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f5])).
% 3.02/1.00  
% 3.02/1.00  fof(f48,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f17])).
% 3.02/1.00  
% 3.02/1.00  fof(f14,conjecture,(
% 3.02/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f15,negated_conjecture,(
% 3.02/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.02/1.00    inference(negated_conjecture,[],[f14])).
% 3.02/1.00  
% 3.02/1.00  fof(f27,plain,(
% 3.02/1.00    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.02/1.00    inference(ennf_transformation,[],[f15])).
% 3.02/1.00  
% 3.02/1.00  fof(f28,plain,(
% 3.02/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.02/1.00    inference(flattening,[],[f27])).
% 3.02/1.00  
% 3.02/1.00  fof(f35,plain,(
% 3.02/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f36,plain,(
% 3.02/1.00    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 3.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f35])).
% 3.02/1.00  
% 3.02/1.00  fof(f64,plain,(
% 3.02/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.02/1.00    inference(cnf_transformation,[],[f36])).
% 3.02/1.00  
% 3.02/1.00  fof(f2,axiom,(
% 3.02/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f45,plain,(
% 3.02/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f2])).
% 3.02/1.00  
% 3.02/1.00  fof(f3,axiom,(
% 3.02/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f46,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f3])).
% 3.02/1.00  
% 3.02/1.00  fof(f4,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f47,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f4])).
% 3.02/1.00  
% 3.02/1.00  fof(f67,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.02/1.00    inference(definition_unfolding,[],[f46,f47])).
% 3.02/1.00  
% 3.02/1.00  fof(f68,plain,(
% 3.02/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.02/1.00    inference(definition_unfolding,[],[f45,f67])).
% 3.02/1.00  
% 3.02/1.00  fof(f80,plain,(
% 3.02/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 3.02/1.00    inference(definition_unfolding,[],[f64,f68])).
% 3.02/1.00  
% 3.02/1.00  fof(f7,axiom,(
% 3.02/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f50,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f7])).
% 3.02/1.00  
% 3.02/1.00  fof(f9,axiom,(
% 3.02/1.00    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f20,plain,(
% 3.02/1.00    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f9])).
% 3.02/1.00  
% 3.02/1.00  fof(f52,plain,(
% 3.02/1.00    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f20])).
% 3.02/1.00  
% 3.02/1.00  fof(f8,axiom,(
% 3.02/1.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f19,plain,(
% 3.02/1.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.02/1.00    inference(ennf_transformation,[],[f8])).
% 3.02/1.00  
% 3.02/1.00  fof(f51,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f19])).
% 3.02/1.00  
% 3.02/1.00  fof(f11,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f23,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f11])).
% 3.02/1.00  
% 3.02/1.00  fof(f54,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f23])).
% 3.02/1.00  
% 3.02/1.00  fof(f63,plain,(
% 3.02/1.00    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 3.02/1.00    inference(cnf_transformation,[],[f36])).
% 3.02/1.00  
% 3.02/1.00  fof(f81,plain,(
% 3.02/1.00    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 3.02/1.00    inference(definition_unfolding,[],[f63,f68])).
% 3.02/1.00  
% 3.02/1.00  fof(f13,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f25,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f13])).
% 3.02/1.00  
% 3.02/1.00  fof(f26,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(flattening,[],[f25])).
% 3.02/1.00  
% 3.02/1.00  fof(f34,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(nnf_transformation,[],[f26])).
% 3.02/1.00  
% 3.02/1.00  fof(f56,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f65,plain,(
% 3.02/1.00    k1_xboole_0 != sK2),
% 3.02/1.00    inference(cnf_transformation,[],[f36])).
% 3.02/1.00  
% 3.02/1.00  fof(f6,axiom,(
% 3.02/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f18,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f6])).
% 3.02/1.00  
% 3.02/1.00  fof(f49,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f18])).
% 3.02/1.00  
% 3.02/1.00  fof(f77,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(definition_unfolding,[],[f49,f68])).
% 3.02/1.00  
% 3.02/1.00  fof(f1,axiom,(
% 3.02/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f16,plain,(
% 3.02/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.02/1.00    inference(ennf_transformation,[],[f1])).
% 3.02/1.00  
% 3.02/1.00  fof(f29,plain,(
% 3.02/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.02/1.00    inference(nnf_transformation,[],[f16])).
% 3.02/1.00  
% 3.02/1.00  fof(f30,plain,(
% 3.02/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.02/1.00    inference(flattening,[],[f29])).
% 3.02/1.00  
% 3.02/1.00  fof(f31,plain,(
% 3.02/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.02/1.00    inference(rectify,[],[f30])).
% 3.02/1.00  
% 3.02/1.00  fof(f32,plain,(
% 3.02/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f33,plain,(
% 3.02/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.02/1.00  
% 3.02/1.00  fof(f38,plain,(
% 3.02/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.02/1.00    inference(cnf_transformation,[],[f33])).
% 3.02/1.00  
% 3.02/1.00  fof(f75,plain,(
% 3.02/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.02/1.00    inference(definition_unfolding,[],[f38,f47])).
% 3.02/1.00  
% 3.02/1.00  fof(f86,plain,(
% 3.02/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.02/1.00    inference(equality_resolution,[],[f75])).
% 3.02/1.00  
% 3.02/1.00  fof(f87,plain,(
% 3.02/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.02/1.00    inference(equality_resolution,[],[f86])).
% 3.02/1.00  
% 3.02/1.00  fof(f10,axiom,(
% 3.02/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f21,plain,(
% 3.02/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.02/1.00    inference(ennf_transformation,[],[f10])).
% 3.02/1.00  
% 3.02/1.00  fof(f22,plain,(
% 3.02/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.02/1.00    inference(flattening,[],[f21])).
% 3.02/1.00  
% 3.02/1.00  fof(f53,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f22])).
% 3.02/1.00  
% 3.02/1.00  fof(f78,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.02/1.00    inference(definition_unfolding,[],[f53,f68])).
% 3.02/1.00  
% 3.02/1.00  fof(f62,plain,(
% 3.02/1.00    v1_funct_1(sK3)),
% 3.02/1.00    inference(cnf_transformation,[],[f36])).
% 3.02/1.00  
% 3.02/1.00  fof(f12,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.02/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f24,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f12])).
% 3.02/1.00  
% 3.02/1.00  fof(f55,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f24])).
% 3.02/1.00  
% 3.02/1.00  fof(f66,plain,(
% 3.02/1.00    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 3.02/1.00    inference(cnf_transformation,[],[f36])).
% 3.02/1.00  
% 3.02/1.00  fof(f79,plain,(
% 3.02/1.00    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 3.02/1.00    inference(definition_unfolding,[],[f66,f68,f68])).
% 3.02/1.00  
% 3.02/1.00  cnf(c_8,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/1.00      | ~ v1_relat_1(X1)
% 3.02/1.00      | v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_24,negated_conjecture,
% 3.02/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 3.02/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_302,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | v1_relat_1(X1)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 3.02/1.00      | sK3 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_303,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | v1_relat_1(sK3)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_302]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1482,plain,
% 3.02/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 3.02/1.00      | v1_relat_1(X0) != iProver_top
% 3.02/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_303]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2051,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
% 3.02/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.02/1.00      inference(equality_resolution,[status(thm)],[c_1482]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2240,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2241,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_2240]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2554,plain,
% 3.02/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2051,c_2241]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 3.02/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1484,plain,
% 3.02/1.00      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2560,plain,
% 3.02/1.00      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2554,c_1484]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1485,plain,
% 3.02/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2559,plain,
% 3.02/1.00      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2554,c_1485]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3923,plain,
% 3.02/1.00      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2560,c_2559]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_14,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_362,plain,
% 3.02/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | sK3 != X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_363,plain,
% 3.02/1.00      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_362]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1654,plain,
% 3.02/1.00      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
% 3.02/1.00      inference(equality_resolution,[status(thm)],[c_363]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_25,negated_conjecture,
% 3.02/1.00      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 3.02/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_21,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.02/1.00      | k1_xboole_0 = X2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_317,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.02/1.00      | sK3 != X0
% 3.02/1.00      | k1_xboole_0 = X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_318,plain,
% 3.02/1.00      ( ~ v1_funct_2(sK3,X0,X1)
% 3.02/1.00      | k1_relset_1(X0,X1,sK3) = X0
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | k1_xboole_0 = X1 ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_317]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_480,plain,
% 3.02/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
% 3.02/1.00      | k1_relset_1(X0,X1,sK3) = X0
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | sK2 != X1
% 3.02/1.00      | sK3 != sK3
% 3.02/1.00      | k1_xboole_0 = X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_318]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_481,plain,
% 3.02/1.00      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 3.02/1.00      | k1_xboole_0 = sK2 ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_480]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_23,negated_conjecture,
% 3.02/1.00      ( k1_xboole_0 != sK2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_482,plain,
% 3.02/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 3.02/1.00      | k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_481,c_23]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_483,plain,
% 3.02/1.00      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_482]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_844,plain,
% 3.02/1.00      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_483]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1958,plain,
% 3.02/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1654,c_844]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_9,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1487,plain,
% 3.02/1.00      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2561,plain,
% 3.02/1.00      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2554,c_1487]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4470,plain,
% 3.02/1.00      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK1) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1958,c_2561]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_8303,plain,
% 3.02/1.00      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_3923,c_4470]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6,plain,
% 3.02/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1489,plain,
% 3.02/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2199,plain,
% 3.02/1.00      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1958,c_1489]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_13,plain,
% 3.02/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.02/1.00      | ~ v1_funct_1(X1)
% 3.02/1.00      | ~ v1_relat_1(X1)
% 3.02/1.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_26,negated_conjecture,
% 3.02/1.00      ( v1_funct_1(sK3) ),
% 3.02/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_283,plain,
% 3.02/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.02/1.00      | ~ v1_relat_1(X1)
% 3.02/1.00      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.02/1.00      | sK3 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_284,plain,
% 3.02/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.02/1.00      | ~ v1_relat_1(sK3)
% 3.02/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_283]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1483,plain,
% 3.02/1.00      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.02/1.00      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.02/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2707,plain,
% 3.02/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1)
% 3.02/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2199,c_1483]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2710,plain,
% 3.02/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k11_relat_1(sK3,sK1) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2707,c_2051,c_2241]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_15,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_353,plain,
% 3.02/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | sK3 != X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_354,plain,
% 3.02/1.00      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_353]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1651,plain,
% 3.02/1.00      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 3.02/1.00      inference(equality_resolution,[status(thm)],[c_354]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_22,negated_conjecture,
% 3.02/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 3.02/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1744,plain,
% 3.02/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1651,c_22]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2713,plain,
% 3.02/1.00      ( k11_relat_1(sK3,sK1) != k2_relat_1(sK3) ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_2710,c_1744]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(contradiction,plain,
% 3.02/1.00      ( $false ),
% 3.02/1.00      inference(minisat,[status(thm)],[c_8303,c_2713]) ).
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  ------                               Statistics
% 3.02/1.00  
% 3.02/1.00  ------ General
% 3.02/1.00  
% 3.02/1.00  abstr_ref_over_cycles:                  0
% 3.02/1.00  abstr_ref_under_cycles:                 0
% 3.02/1.00  gc_basic_clause_elim:                   0
% 3.02/1.00  forced_gc_time:                         0
% 3.02/1.00  parsing_time:                           0.009
% 3.02/1.00  unif_index_cands_time:                  0.
% 3.02/1.00  unif_index_add_time:                    0.
% 3.02/1.00  orderings_time:                         0.
% 3.02/1.00  out_proof_time:                         0.008
% 3.02/1.00  total_time:                             0.288
% 3.02/1.00  num_of_symbols:                         52
% 3.02/1.00  num_of_terms:                           9271
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing
% 3.02/1.00  
% 3.02/1.00  num_of_splits:                          0
% 3.02/1.00  num_of_split_atoms:                     0
% 3.02/1.00  num_of_reused_defs:                     0
% 3.02/1.00  num_eq_ax_congr_red:                    25
% 3.02/1.00  num_of_sem_filtered_clauses:            1
% 3.02/1.00  num_of_subtypes:                        0
% 3.02/1.00  monotx_restored_types:                  0
% 3.02/1.00  sat_num_of_epr_types:                   0
% 3.02/1.00  sat_num_of_non_cyclic_types:            0
% 3.02/1.00  sat_guarded_non_collapsed_types:        0
% 3.02/1.00  num_pure_diseq_elim:                    0
% 3.02/1.00  simp_replaced_by:                       0
% 3.02/1.00  res_preprocessed:                       121
% 3.02/1.00  prep_upred:                             0
% 3.02/1.00  prep_unflattend:                        64
% 3.02/1.00  smt_new_axioms:                         0
% 3.02/1.00  pred_elim_cands:                        2
% 3.02/1.00  pred_elim:                              3
% 3.02/1.00  pred_elim_cl:                           6
% 3.02/1.00  pred_elim_cycles:                       5
% 3.02/1.00  merged_defs:                            0
% 3.02/1.00  merged_defs_ncl:                        0
% 3.02/1.00  bin_hyper_res:                          0
% 3.02/1.00  prep_cycles:                            4
% 3.02/1.00  pred_elim_time:                         0.02
% 3.02/1.00  splitting_time:                         0.
% 3.02/1.00  sem_filter_time:                        0.
% 3.02/1.00  monotx_time:                            0.
% 3.02/1.00  subtype_inf_time:                       0.
% 3.02/1.00  
% 3.02/1.00  ------ Problem properties
% 3.02/1.00  
% 3.02/1.00  clauses:                                21
% 3.02/1.00  conjectures:                            2
% 3.02/1.00  epr:                                    1
% 3.02/1.00  horn:                                   18
% 3.02/1.00  ground:                                 5
% 3.02/1.00  unary:                                  7
% 3.02/1.00  binary:                                 5
% 3.02/1.00  lits:                                   48
% 3.02/1.00  lits_eq:                                32
% 3.02/1.00  fd_pure:                                0
% 3.02/1.00  fd_pseudo:                              0
% 3.02/1.00  fd_cond:                                0
% 3.02/1.00  fd_pseudo_cond:                         4
% 3.02/1.00  ac_symbols:                             0
% 3.02/1.00  
% 3.02/1.00  ------ Propositional Solver
% 3.02/1.00  
% 3.02/1.00  prop_solver_calls:                      28
% 3.02/1.00  prop_fast_solver_calls:                 908
% 3.02/1.00  smt_solver_calls:                       0
% 3.02/1.00  smt_fast_solver_calls:                  0
% 3.02/1.00  prop_num_of_clauses:                    2611
% 3.02/1.00  prop_preprocess_simplified:             8498
% 3.02/1.00  prop_fo_subsumed:                       10
% 3.02/1.00  prop_solver_time:                       0.
% 3.02/1.00  smt_solver_time:                        0.
% 3.02/1.00  smt_fast_solver_time:                   0.
% 3.02/1.00  prop_fast_solver_time:                  0.
% 3.02/1.00  prop_unsat_core_time:                   0.
% 3.02/1.00  
% 3.02/1.00  ------ QBF
% 3.02/1.00  
% 3.02/1.00  qbf_q_res:                              0
% 3.02/1.00  qbf_num_tautologies:                    0
% 3.02/1.00  qbf_prep_cycles:                        0
% 3.02/1.00  
% 3.02/1.00  ------ BMC1
% 3.02/1.00  
% 3.02/1.00  bmc1_current_bound:                     -1
% 3.02/1.00  bmc1_last_solved_bound:                 -1
% 3.02/1.00  bmc1_unsat_core_size:                   -1
% 3.02/1.00  bmc1_unsat_core_parents_size:           -1
% 3.02/1.00  bmc1_merge_next_fun:                    0
% 3.02/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation
% 3.02/1.00  
% 3.02/1.00  inst_num_of_clauses:                    866
% 3.02/1.00  inst_num_in_passive:                    382
% 3.02/1.00  inst_num_in_active:                     288
% 3.02/1.00  inst_num_in_unprocessed:                196
% 3.02/1.00  inst_num_of_loops:                      300
% 3.02/1.00  inst_num_of_learning_restarts:          0
% 3.02/1.00  inst_num_moves_active_passive:          10
% 3.02/1.00  inst_lit_activity:                      0
% 3.02/1.00  inst_lit_activity_moves:                0
% 3.02/1.00  inst_num_tautologies:                   0
% 3.02/1.00  inst_num_prop_implied:                  0
% 3.02/1.00  inst_num_existing_simplified:           0
% 3.02/1.00  inst_num_eq_res_simplified:             0
% 3.02/1.00  inst_num_child_elim:                    0
% 3.02/1.00  inst_num_of_dismatching_blockings:      398
% 3.02/1.00  inst_num_of_non_proper_insts:           903
% 3.02/1.00  inst_num_of_duplicates:                 0
% 3.02/1.00  inst_inst_num_from_inst_to_res:         0
% 3.02/1.00  inst_dismatching_checking_time:         0.
% 3.02/1.00  
% 3.02/1.00  ------ Resolution
% 3.02/1.00  
% 3.02/1.00  res_num_of_clauses:                     0
% 3.02/1.00  res_num_in_passive:                     0
% 3.02/1.00  res_num_in_active:                      0
% 3.02/1.00  res_num_of_loops:                       125
% 3.02/1.00  res_forward_subset_subsumed:            133
% 3.02/1.00  res_backward_subset_subsumed:           0
% 3.02/1.00  res_forward_subsumed:                   0
% 3.02/1.00  res_backward_subsumed:                  0
% 3.02/1.00  res_forward_subsumption_resolution:     0
% 3.02/1.00  res_backward_subsumption_resolution:    0
% 3.02/1.00  res_clause_to_clause_subsumption:       1056
% 3.02/1.00  res_orphan_elimination:                 0
% 3.02/1.00  res_tautology_del:                      75
% 3.02/1.00  res_num_eq_res_simplified:              1
% 3.02/1.00  res_num_sel_changes:                    0
% 3.02/1.00  res_moves_from_active_to_pass:          0
% 3.02/1.00  
% 3.02/1.00  ------ Superposition
% 3.02/1.00  
% 3.02/1.00  sup_time_total:                         0.
% 3.02/1.00  sup_time_generating:                    0.
% 3.02/1.00  sup_time_sim_full:                      0.
% 3.02/1.00  sup_time_sim_immed:                     0.
% 3.02/1.00  
% 3.02/1.00  sup_num_of_clauses:                     133
% 3.02/1.00  sup_num_in_active:                      49
% 3.02/1.00  sup_num_in_passive:                     84
% 3.02/1.00  sup_num_of_loops:                       59
% 3.02/1.00  sup_fw_superposition:                   119
% 3.02/1.00  sup_bw_superposition:                   282
% 3.02/1.00  sup_immediate_simplified:               156
% 3.02/1.00  sup_given_eliminated:                   0
% 3.02/1.00  comparisons_done:                       0
% 3.02/1.00  comparisons_avoided:                    108
% 3.02/1.00  
% 3.02/1.00  ------ Simplifications
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  sim_fw_subset_subsumed:                 69
% 3.02/1.00  sim_bw_subset_subsumed:                 0
% 3.02/1.00  sim_fw_subsumed:                        63
% 3.02/1.00  sim_bw_subsumed:                        10
% 3.02/1.00  sim_fw_subsumption_res:                 0
% 3.02/1.00  sim_bw_subsumption_res:                 0
% 3.02/1.00  sim_tautology_del:                      0
% 3.02/1.00  sim_eq_tautology_del:                   3
% 3.02/1.00  sim_eq_res_simp:                        0
% 3.02/1.00  sim_fw_demodulated:                     9
% 3.02/1.00  sim_bw_demodulated:                     10
% 3.02/1.00  sim_light_normalised:                   9
% 3.02/1.00  sim_joinable_taut:                      0
% 3.02/1.00  sim_joinable_simp:                      0
% 3.02/1.00  sim_ac_normalised:                      0
% 3.02/1.00  sim_smt_subsumption:                    0
% 3.02/1.00  
%------------------------------------------------------------------------------
