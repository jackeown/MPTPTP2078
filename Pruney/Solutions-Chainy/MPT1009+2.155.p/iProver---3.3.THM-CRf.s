%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:59 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 729 expanded)
%              Number of clauses        :   66 ( 206 expanded)
%              Number of leaves         :   16 ( 163 expanded)
%              Depth                    :   24
%              Number of atoms          :  367 (2363 expanded)
%              Number of equality atoms :  210 ( 965 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK4,k1_tarski(sK1),sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f33])).

fof(f58,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f73,plain,(
    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f58,f62])).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f60,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f76,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f77,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f76])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f61,f62,f62])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1246,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_323,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_324,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_658,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_enumset1(sK1,sK1,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | sK2 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_324])).

cnf(c_659,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_660,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_659,c_21])).

cnf(c_661,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_660])).

cnf(c_723,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_661])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_368,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_369,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_1376,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_369])).

cnf(c_1461,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_723,c_1376])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_308,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_309,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_1242,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_1553,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1242,c_1461])).

cnf(c_1560,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1553])).

cnf(c_987,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1377,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_987])).

cnf(c_1368,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1511,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1512,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1511])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1611,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1612,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1611])).

cnf(c_3099,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1560,c_1377,c_1512,c_1612])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1248,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3104,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3099,c_1248])).

cnf(c_3579,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1461,c_3104])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1245,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3105,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_3099,c_1245])).

cnf(c_3589,plain,
    ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_3579,c_3105])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1250,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1637,plain,
    ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_1250])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_289,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_1243,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_291,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_1942,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1243,c_291,c_1377,c_1512,c_1612])).

cnf(c_1943,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1942])).

cnf(c_2025,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1637,c_1943])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1244,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1466,plain,
    ( r1_tarski(k7_relset_1(k1_relat_1(sK4),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1461,c_1244])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_359,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_360,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_1408,plain,
    ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_360])).

cnf(c_1694,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_1408,c_1461])).

cnf(c_1787,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1466,c_1694])).

cnf(c_2587,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2025,c_1787])).

cnf(c_5614,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3589,c_2587])).

cnf(c_5787,plain,
    ( v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_5614])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5787,c_1612,c_1512,c_1377])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
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
% 3.02/0.99  clauses                                 19
% 3.02/0.99  conjectures                             2
% 3.02/0.99  EPR                                     1
% 3.02/0.99  Horn                                    16
% 3.02/0.99  unary                                   6
% 3.02/0.99  binary                                  5
% 3.02/0.99  lits                                    42
% 3.02/0.99  lits eq                                 26
% 3.02/0.99  fd_pure                                 0
% 3.02/0.99  fd_pseudo                               0
% 3.02/0.99  fd_cond                                 0
% 3.02/0.99  fd_pseudo_cond                          3
% 3.02/0.99  AC symbols                              0
% 3.02/0.99  
% 3.02/0.99  ------ Schedule dynamic 5 is on 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  Current options:
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
% 3.02/1.00  fof(f7,axiom,(
% 3.02/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f17,plain,(
% 3.02/1.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.02/1.00    inference(ennf_transformation,[],[f7])).
% 3.02/1.00  
% 3.02/1.00  fof(f46,plain,(
% 3.02/1.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f17])).
% 3.02/1.00  
% 3.02/1.00  fof(f13,conjecture,(
% 3.02/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f14,negated_conjecture,(
% 3.02/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.02/1.00    inference(negated_conjecture,[],[f13])).
% 3.02/1.00  
% 3.02/1.00  fof(f25,plain,(
% 3.02/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 3.02/1.00    inference(ennf_transformation,[],[f14])).
% 3.02/1.00  
% 3.02/1.00  fof(f26,plain,(
% 3.02/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 3.02/1.00    inference(flattening,[],[f25])).
% 3.02/1.00  
% 3.02/1.00  fof(f33,plain,(
% 3.02/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f34,plain,(
% 3.02/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 3.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f26,f33])).
% 3.02/1.00  
% 3.02/1.00  fof(f58,plain,(
% 3.02/1.00    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 3.02/1.00    inference(cnf_transformation,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f2,axiom,(
% 3.02/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f41,plain,(
% 3.02/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f2])).
% 3.02/1.00  
% 3.02/1.00  fof(f3,axiom,(
% 3.02/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f42,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f3])).
% 3.02/1.00  
% 3.02/1.00  fof(f62,plain,(
% 3.02/1.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.02/1.00    inference(definition_unfolding,[],[f41,f42])).
% 3.02/1.00  
% 3.02/1.00  fof(f73,plain,(
% 3.02/1.00    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2)),
% 3.02/1.00    inference(definition_unfolding,[],[f58,f62])).
% 3.02/1.00  
% 3.02/1.00  fof(f12,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f23,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f12])).
% 3.02/1.00  
% 3.02/1.00  fof(f24,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(flattening,[],[f23])).
% 3.02/1.00  
% 3.02/1.00  fof(f32,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(nnf_transformation,[],[f24])).
% 3.02/1.00  
% 3.02/1.00  fof(f51,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f32])).
% 3.02/1.00  
% 3.02/1.00  fof(f59,plain,(
% 3.02/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.02/1.00    inference(cnf_transformation,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f72,plain,(
% 3.02/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 3.02/1.00    inference(definition_unfolding,[],[f59,f62])).
% 3.02/1.00  
% 3.02/1.00  fof(f60,plain,(
% 3.02/1.00    k1_xboole_0 != sK2),
% 3.02/1.00    inference(cnf_transformation,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f10,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f21,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f10])).
% 3.02/1.00  
% 3.02/1.00  fof(f49,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f21])).
% 3.02/1.00  
% 3.02/1.00  fof(f4,axiom,(
% 3.02/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f15,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f4])).
% 3.02/1.00  
% 3.02/1.00  fof(f43,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f15])).
% 3.02/1.00  
% 3.02/1.00  fof(f6,axiom,(
% 3.02/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f45,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f6])).
% 3.02/1.00  
% 3.02/1.00  fof(f5,axiom,(
% 3.02/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f16,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f5])).
% 3.02/1.00  
% 3.02/1.00  fof(f44,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f16])).
% 3.02/1.00  
% 3.02/1.00  fof(f69,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(definition_unfolding,[],[f44,f62])).
% 3.02/1.00  
% 3.02/1.00  fof(f8,axiom,(
% 3.02/1.00    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f18,plain,(
% 3.02/1.00    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f8])).
% 3.02/1.00  
% 3.02/1.00  fof(f47,plain,(
% 3.02/1.00    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f18])).
% 3.02/1.00  
% 3.02/1.00  fof(f1,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f27,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.02/1.00    inference(nnf_transformation,[],[f1])).
% 3.02/1.00  
% 3.02/1.00  fof(f28,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.02/1.00    inference(flattening,[],[f27])).
% 3.02/1.00  
% 3.02/1.00  fof(f29,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.02/1.00    inference(rectify,[],[f28])).
% 3.02/1.00  
% 3.02/1.00  fof(f30,plain,(
% 3.02/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f31,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 3.02/1.00  
% 3.02/1.00  fof(f36,plain,(
% 3.02/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.02/1.00    inference(cnf_transformation,[],[f31])).
% 3.02/1.00  
% 3.02/1.00  fof(f67,plain,(
% 3.02/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.02/1.00    inference(definition_unfolding,[],[f36,f42])).
% 3.02/1.00  
% 3.02/1.00  fof(f76,plain,(
% 3.02/1.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 3.02/1.00    inference(equality_resolution,[],[f67])).
% 3.02/1.00  
% 3.02/1.00  fof(f77,plain,(
% 3.02/1.00    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 3.02/1.00    inference(equality_resolution,[],[f76])).
% 3.02/1.00  
% 3.02/1.00  fof(f9,axiom,(
% 3.02/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f19,plain,(
% 3.02/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.02/1.00    inference(ennf_transformation,[],[f9])).
% 3.02/1.00  
% 3.02/1.00  fof(f20,plain,(
% 3.02/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.02/1.00    inference(flattening,[],[f19])).
% 3.02/1.00  
% 3.02/1.00  fof(f48,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f20])).
% 3.02/1.00  
% 3.02/1.00  fof(f70,plain,(
% 3.02/1.00    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.02/1.00    inference(definition_unfolding,[],[f48,f62])).
% 3.02/1.00  
% 3.02/1.00  fof(f57,plain,(
% 3.02/1.00    v1_funct_1(sK4)),
% 3.02/1.00    inference(cnf_transformation,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f61,plain,(
% 3.02/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 3.02/1.00    inference(cnf_transformation,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f71,plain,(
% 3.02/1.00    ~r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 3.02/1.00    inference(definition_unfolding,[],[f61,f62,f62])).
% 3.02/1.00  
% 3.02/1.00  fof(f11,axiom,(
% 3.02/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f22,plain,(
% 3.02/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f11])).
% 3.02/1.00  
% 3.02/1.00  fof(f50,plain,(
% 3.02/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f22])).
% 3.02/1.00  
% 3.02/1.00  cnf(c_9,plain,
% 3.02/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1246,plain,
% 3.02/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_23,negated_conjecture,
% 3.02/1.00      ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 3.02/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_19,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.02/1.00      | k1_xboole_0 = X2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_22,negated_conjecture,
% 3.02/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 3.02/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_323,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.02/1.00      | sK4 != X0
% 3.02/1.00      | k1_xboole_0 = X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_324,plain,
% 3.02/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.02/1.00      | k1_relset_1(X0,X1,sK4) = X0
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | k1_xboole_0 = X1 ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_658,plain,
% 3.02/1.00      ( k1_relset_1(X0,X1,sK4) = X0
% 3.02/1.00      | k1_enumset1(sK1,sK1,sK1) != X0
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | sK4 != sK4
% 3.02/1.00      | sK2 != X1
% 3.02/1.00      | k1_xboole_0 = X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_324]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_659,plain,
% 3.02/1.00      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.02/1.00      | k1_xboole_0 = sK2 ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_658]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_21,negated_conjecture,
% 3.02/1.00      ( k1_xboole_0 != sK2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_660,plain,
% 3.02/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.02/1.00      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_659,c_21]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_661,plain,
% 3.02/1.00      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_660]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_723,plain,
% 3.02/1.00      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_661]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_368,plain,
% 3.02/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | sK4 != X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_369,plain,
% 3.02/1.00      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_368]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1376,plain,
% 3.02/1.00      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
% 3.02/1.00      inference(equality_resolution,[status(thm)],[c_369]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1461,plain,
% 3.02/1.00      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_723,c_1376]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/1.00      | ~ v1_relat_1(X1)
% 3.02/1.00      | v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_308,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | v1_relat_1(X1)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 3.02/1.00      | sK4 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_309,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | v1_relat_1(sK4)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_308]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1242,plain,
% 3.02/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 3.02/1.00      | v1_relat_1(X0) != iProver_top
% 3.02/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1553,plain,
% 3.02/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)) != k1_zfmisc_1(X0)
% 3.02/1.00      | v1_relat_1(X0) != iProver_top
% 3.02/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_1242,c_1461]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1560,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)) != iProver_top
% 3.02/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.02/1.00      inference(equality_resolution,[status(thm)],[c_1553]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_987,plain,( X0 = X0 ),theory(equality) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1377,plain,
% 3.02/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_987]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1368,plain,
% 3.02/1.00      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | v1_relat_1(sK4)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_309]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1511,plain,
% 3.02/1.00      ( ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.02/1.00      | v1_relat_1(sK4)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_1368]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1512,plain,
% 3.02/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 3.02/1.00      | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != iProver_top
% 3.02/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1511]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_8,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1611,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1612,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1611]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3099,plain,
% 3.02/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_1560,c_1377,c_1512,c_1612]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_7,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1248,plain,
% 3.02/1.00      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3104,plain,
% 3.02/1.00      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_3099,c_1248]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3579,plain,
% 3.02/1.00      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1461,c_3104]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10,plain,
% 3.02/1.00      ( ~ v1_relat_1(X0)
% 3.02/1.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1245,plain,
% 3.02/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.02/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3105,plain,
% 3.02/1.00      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_3099,c_1245]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3589,plain,
% 3.02/1.00      ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_3579,c_3105]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4,plain,
% 3.02/1.00      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1250,plain,
% 3.02/1.00      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1637,plain,
% 3.02/1.00      ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1461,c_1250]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11,plain,
% 3.02/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.02/1.00      | ~ v1_funct_1(X1)
% 3.02/1.00      | ~ v1_relat_1(X1)
% 3.02/1.00      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_24,negated_conjecture,
% 3.02/1.00      ( v1_funct_1(sK4) ),
% 3.02/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_289,plain,
% 3.02/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.02/1.00      | ~ v1_relat_1(X1)
% 3.02/1.00      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.02/1.00      | sK4 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_290,plain,
% 3.02/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.02/1.00      | ~ v1_relat_1(sK4)
% 3.02/1.00      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_289]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1243,plain,
% 3.02/1.00      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.02/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.02/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_291,plain,
% 3.02/1.00      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.02/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.02/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1942,plain,
% 3.02/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.02/1.00      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_1243,c_291,c_1377,c_1512,c_1612]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1943,plain,
% 3.02/1.00      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.02/1.00      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_1942]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2025,plain,
% 3.02/1.00      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1637,c_1943]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_20,negated_conjecture,
% 3.02/1.00      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 3.02/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1244,plain,
% 3.02/1.00      ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1466,plain,
% 3.02/1.00      ( r1_tarski(k7_relset_1(k1_relat_1(sK4),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1461,c_1244]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_13,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.02/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_359,plain,
% 3.02/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.02/1.00      | sK4 != X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_360,plain,
% 3.02/1.00      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 3.02/1.00      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_359]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1408,plain,
% 3.02/1.00      ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.02/1.00      inference(equality_resolution,[status(thm)],[c_360]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1694,plain,
% 3.02/1.00      ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_1408,c_1461]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1787,plain,
% 3.02/1.00      ( r1_tarski(k9_relat_1(sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1466,c_1694]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2587,plain,
% 3.02/1.00      ( r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_2025,c_1787]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5614,plain,
% 3.02/1.00      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_3589,c_2587]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5787,plain,
% 3.02/1.00      ( v1_relat_1(sK4) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1246,c_5614]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(contradiction,plain,
% 3.02/1.00      ( $false ),
% 3.02/1.00      inference(minisat,[status(thm)],[c_5787,c_1612,c_1512,c_1377]) ).
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
% 3.02/1.00  parsing_time:                           0.011
% 3.02/1.00  unif_index_cands_time:                  0.
% 3.02/1.00  unif_index_add_time:                    0.
% 3.02/1.00  orderings_time:                         0.
% 3.02/1.00  out_proof_time:                         0.013
% 3.02/1.00  total_time:                             0.275
% 3.02/1.00  num_of_symbols:                         53
% 3.02/1.00  num_of_terms:                           7173
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing
% 3.02/1.00  
% 3.02/1.00  num_of_splits:                          0
% 3.02/1.00  num_of_split_atoms:                     0
% 3.02/1.00  num_of_reused_defs:                     0
% 3.02/1.00  num_eq_ax_congr_red:                    20
% 3.02/1.00  num_of_sem_filtered_clauses:            1
% 3.02/1.00  num_of_subtypes:                        0
% 3.02/1.00  monotx_restored_types:                  0
% 3.02/1.00  sat_num_of_epr_types:                   0
% 3.02/1.00  sat_num_of_non_cyclic_types:            0
% 3.02/1.00  sat_guarded_non_collapsed_types:        0
% 3.02/1.00  num_pure_diseq_elim:                    0
% 3.02/1.00  simp_replaced_by:                       0
% 3.02/1.00  res_preprocessed:                       111
% 3.02/1.00  prep_upred:                             0
% 3.02/1.00  prep_unflattend:                        50
% 3.02/1.00  smt_new_axioms:                         0
% 3.02/1.00  pred_elim_cands:                        3
% 3.02/1.00  pred_elim:                              3
% 3.02/1.00  pred_elim_cl:                           6
% 3.02/1.00  pred_elim_cycles:                       8
% 3.02/1.00  merged_defs:                            0
% 3.02/1.00  merged_defs_ncl:                        0
% 3.02/1.00  bin_hyper_res:                          0
% 3.02/1.00  prep_cycles:                            4
% 3.02/1.00  pred_elim_time:                         0.011
% 3.02/1.00  splitting_time:                         0.
% 3.02/1.00  sem_filter_time:                        0.
% 3.02/1.00  monotx_time:                            0.001
% 3.02/1.00  subtype_inf_time:                       0.
% 3.02/1.00  
% 3.02/1.00  ------ Problem properties
% 3.02/1.00  
% 3.02/1.00  clauses:                                19
% 3.02/1.00  conjectures:                            2
% 3.02/1.00  epr:                                    1
% 3.02/1.00  horn:                                   16
% 3.02/1.00  ground:                                 5
% 3.02/1.00  unary:                                  6
% 3.02/1.00  binary:                                 5
% 3.02/1.00  lits:                                   42
% 3.02/1.00  lits_eq:                                26
% 3.02/1.00  fd_pure:                                0
% 3.02/1.00  fd_pseudo:                              0
% 3.02/1.00  fd_cond:                                0
% 3.02/1.00  fd_pseudo_cond:                         3
% 3.02/1.00  ac_symbols:                             0
% 3.02/1.00  
% 3.02/1.00  ------ Propositional Solver
% 3.02/1.00  
% 3.02/1.00  prop_solver_calls:                      28
% 3.02/1.00  prop_fast_solver_calls:                 799
% 3.02/1.00  smt_solver_calls:                       0
% 3.02/1.00  smt_fast_solver_calls:                  0
% 3.02/1.00  prop_num_of_clauses:                    2066
% 3.02/1.00  prop_preprocess_simplified:             7122
% 3.02/1.00  prop_fo_subsumed:                       11
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
% 3.02/1.00  inst_num_of_clauses:                    653
% 3.02/1.00  inst_num_in_passive:                    337
% 3.02/1.00  inst_num_in_active:                     274
% 3.02/1.00  inst_num_in_unprocessed:                42
% 3.02/1.00  inst_num_of_loops:                      280
% 3.02/1.00  inst_num_of_learning_restarts:          0
% 3.02/1.00  inst_num_moves_active_passive:          4
% 3.02/1.00  inst_lit_activity:                      0
% 3.02/1.00  inst_lit_activity_moves:                0
% 3.02/1.00  inst_num_tautologies:                   0
% 3.02/1.00  inst_num_prop_implied:                  0
% 3.02/1.00  inst_num_existing_simplified:           0
% 3.02/1.00  inst_num_eq_res_simplified:             0
% 3.02/1.00  inst_num_child_elim:                    0
% 3.02/1.00  inst_num_of_dismatching_blockings:      408
% 3.02/1.00  inst_num_of_non_proper_insts:           759
% 3.02/1.00  inst_num_of_duplicates:                 0
% 3.02/1.00  inst_inst_num_from_inst_to_res:         0
% 3.02/1.00  inst_dismatching_checking_time:         0.
% 3.02/1.00  
% 3.02/1.00  ------ Resolution
% 3.02/1.00  
% 3.02/1.00  res_num_of_clauses:                     0
% 3.02/1.00  res_num_in_passive:                     0
% 3.02/1.00  res_num_in_active:                      0
% 3.02/1.00  res_num_of_loops:                       115
% 3.02/1.00  res_forward_subset_subsumed:            167
% 3.02/1.00  res_backward_subset_subsumed:           0
% 3.02/1.00  res_forward_subsumed:                   0
% 3.02/1.00  res_backward_subsumed:                  0
% 3.02/1.00  res_forward_subsumption_resolution:     0
% 3.02/1.00  res_backward_subsumption_resolution:    0
% 3.02/1.00  res_clause_to_clause_subsumption:       179
% 3.02/1.00  res_orphan_elimination:                 0
% 3.02/1.00  res_tautology_del:                      54
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
% 3.02/1.00  sup_num_of_clauses:                     69
% 3.02/1.00  sup_num_in_active:                      43
% 3.02/1.00  sup_num_in_passive:                     26
% 3.02/1.00  sup_num_of_loops:                       55
% 3.02/1.00  sup_fw_superposition:                   22
% 3.02/1.00  sup_bw_superposition:                   49
% 3.02/1.00  sup_immediate_simplified:               9
% 3.02/1.00  sup_given_eliminated:                   0
% 3.02/1.00  comparisons_done:                       0
% 3.02/1.00  comparisons_avoided:                    97
% 3.02/1.00  
% 3.02/1.00  ------ Simplifications
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  sim_fw_subset_subsumed:                 0
% 3.02/1.00  sim_bw_subset_subsumed:                 0
% 3.02/1.00  sim_fw_subsumed:                        4
% 3.02/1.00  sim_bw_subsumed:                        0
% 3.02/1.00  sim_fw_subsumption_res:                 0
% 3.02/1.00  sim_bw_subsumption_res:                 0
% 3.02/1.00  sim_tautology_del:                      0
% 3.02/1.00  sim_eq_tautology_del:                   4
% 3.02/1.00  sim_eq_res_simp:                        0
% 3.02/1.00  sim_fw_demodulated:                     3
% 3.02/1.00  sim_bw_demodulated:                     14
% 3.02/1.00  sim_light_normalised:                   6
% 3.02/1.00  sim_joinable_taut:                      0
% 3.02/1.00  sim_joinable_simp:                      0
% 3.02/1.00  sim_ac_normalised:                      0
% 3.02/1.00  sim_smt_subsumption:                    0
% 3.02/1.00  
%------------------------------------------------------------------------------
