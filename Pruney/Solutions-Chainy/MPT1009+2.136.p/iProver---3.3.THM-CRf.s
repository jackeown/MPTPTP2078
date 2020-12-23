%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:55 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 673 expanded)
%              Number of clauses        :   73 ( 177 expanded)
%              Number of leaves         :   19 ( 159 expanded)
%              Depth                    :   22
%              Number of atoms          :  410 (1913 expanded)
%              Number of equality atoms :  228 ( 783 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,
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

fof(f41,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f33,f40])).

fof(f68,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f84,plain,(
    v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f15,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f70,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f87,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f78])).

fof(f88,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f87])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f71,f73,f73])).

cnf(c_9,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1333,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_380,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_381,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_718,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | sK2 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_381])).

cnf(c_719,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_720,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_23])).

cnf(c_721,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_720])).

cnf(c_784,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_721])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_425,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_426,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_1466,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_426])).

cnf(c_1583,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_784,c_1466])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_350,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_351,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_1329,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_1055,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1472,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_1467,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_1580,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_1581,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1580])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1714,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1715,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_1948,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1329,c_1472,c_1581,c_1715])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1335,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2183,plain,
    ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1948,c_1335])).

cnf(c_2669,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1583,c_2183])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_365,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_24])).

cnf(c_366,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_1328,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_2020,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k7_relat_1(sK4,X0) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1328,c_366,c_1472,c_1580,c_1714])).

cnf(c_2021,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(renaming,[status(thm)],[c_2020])).

cnf(c_2023,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2021,c_1583])).

cnf(c_2027,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_2023])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1332,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1953,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1948,c_1332])).

cnf(c_3286,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2027,c_1953])).

cnf(c_3911,plain,
    ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2669,c_3286])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1337,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1703,plain,
    ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_1337])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_332,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_1330,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_333,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_2029,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1330,c_333,c_1472,c_1581,c_1715])).

cnf(c_2030,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2029])).

cnf(c_2682,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1703,c_2030])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_416,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_417,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_1495,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_417])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1331,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1561,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1495,c_1331])).

cnf(c_2903,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2682,c_1561])).

cnf(c_3914,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3911,c_2903])).

cnf(c_3926,plain,
    ( v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_3914])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3926,c_1715,c_1581,c_1472])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.76/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.04  
% 2.76/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/1.04  
% 2.76/1.04  ------  iProver source info
% 2.76/1.04  
% 2.76/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.76/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/1.04  git: non_committed_changes: false
% 2.76/1.04  git: last_make_outside_of_git: false
% 2.76/1.04  
% 2.76/1.04  ------ 
% 2.76/1.04  
% 2.76/1.04  ------ Input Options
% 2.76/1.04  
% 2.76/1.04  --out_options                           all
% 2.76/1.04  --tptp_safe_out                         true
% 2.76/1.04  --problem_path                          ""
% 2.76/1.04  --include_path                          ""
% 2.76/1.04  --clausifier                            res/vclausify_rel
% 2.76/1.04  --clausifier_options                    --mode clausify
% 2.76/1.04  --stdin                                 false
% 2.76/1.04  --stats_out                             all
% 2.76/1.04  
% 2.76/1.04  ------ General Options
% 2.76/1.04  
% 2.76/1.04  --fof                                   false
% 2.76/1.04  --time_out_real                         305.
% 2.76/1.04  --time_out_virtual                      -1.
% 2.76/1.04  --symbol_type_check                     false
% 2.76/1.04  --clausify_out                          false
% 2.76/1.04  --sig_cnt_out                           false
% 2.76/1.04  --trig_cnt_out                          false
% 2.76/1.04  --trig_cnt_out_tolerance                1.
% 2.76/1.04  --trig_cnt_out_sk_spl                   false
% 2.76/1.04  --abstr_cl_out                          false
% 2.76/1.04  
% 2.76/1.04  ------ Global Options
% 2.76/1.04  
% 2.76/1.04  --schedule                              default
% 2.76/1.04  --add_important_lit                     false
% 2.76/1.04  --prop_solver_per_cl                    1000
% 2.76/1.04  --min_unsat_core                        false
% 2.76/1.04  --soft_assumptions                      false
% 2.76/1.04  --soft_lemma_size                       3
% 2.76/1.04  --prop_impl_unit_size                   0
% 2.76/1.04  --prop_impl_unit                        []
% 2.76/1.04  --share_sel_clauses                     true
% 2.76/1.04  --reset_solvers                         false
% 2.76/1.04  --bc_imp_inh                            [conj_cone]
% 2.76/1.04  --conj_cone_tolerance                   3.
% 2.76/1.04  --extra_neg_conj                        none
% 2.76/1.04  --large_theory_mode                     true
% 2.76/1.04  --prolific_symb_bound                   200
% 2.76/1.04  --lt_threshold                          2000
% 2.76/1.04  --clause_weak_htbl                      true
% 2.76/1.04  --gc_record_bc_elim                     false
% 2.76/1.04  
% 2.76/1.04  ------ Preprocessing Options
% 2.76/1.04  
% 2.76/1.04  --preprocessing_flag                    true
% 2.76/1.04  --time_out_prep_mult                    0.1
% 2.76/1.04  --splitting_mode                        input
% 2.76/1.04  --splitting_grd                         true
% 2.76/1.04  --splitting_cvd                         false
% 2.76/1.04  --splitting_cvd_svl                     false
% 2.76/1.04  --splitting_nvd                         32
% 2.76/1.04  --sub_typing                            true
% 2.76/1.04  --prep_gs_sim                           true
% 2.76/1.04  --prep_unflatten                        true
% 2.76/1.04  --prep_res_sim                          true
% 2.76/1.04  --prep_upred                            true
% 2.76/1.04  --prep_sem_filter                       exhaustive
% 2.76/1.04  --prep_sem_filter_out                   false
% 2.76/1.04  --pred_elim                             true
% 2.76/1.04  --res_sim_input                         true
% 2.76/1.04  --eq_ax_congr_red                       true
% 2.76/1.04  --pure_diseq_elim                       true
% 2.76/1.04  --brand_transform                       false
% 2.76/1.04  --non_eq_to_eq                          false
% 2.76/1.04  --prep_def_merge                        true
% 2.76/1.04  --prep_def_merge_prop_impl              false
% 2.76/1.04  --prep_def_merge_mbd                    true
% 2.76/1.04  --prep_def_merge_tr_red                 false
% 2.76/1.04  --prep_def_merge_tr_cl                  false
% 2.76/1.04  --smt_preprocessing                     true
% 2.76/1.04  --smt_ac_axioms                         fast
% 2.76/1.04  --preprocessed_out                      false
% 2.76/1.04  --preprocessed_stats                    false
% 2.76/1.04  
% 2.76/1.04  ------ Abstraction refinement Options
% 2.76/1.04  
% 2.76/1.04  --abstr_ref                             []
% 2.76/1.04  --abstr_ref_prep                        false
% 2.76/1.04  --abstr_ref_until_sat                   false
% 2.76/1.04  --abstr_ref_sig_restrict                funpre
% 2.76/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.04  --abstr_ref_under                       []
% 2.76/1.04  
% 2.76/1.04  ------ SAT Options
% 2.76/1.04  
% 2.76/1.04  --sat_mode                              false
% 2.76/1.04  --sat_fm_restart_options                ""
% 2.76/1.04  --sat_gr_def                            false
% 2.76/1.04  --sat_epr_types                         true
% 2.76/1.04  --sat_non_cyclic_types                  false
% 2.76/1.04  --sat_finite_models                     false
% 2.76/1.04  --sat_fm_lemmas                         false
% 2.76/1.04  --sat_fm_prep                           false
% 2.76/1.04  --sat_fm_uc_incr                        true
% 2.76/1.04  --sat_out_model                         small
% 2.76/1.04  --sat_out_clauses                       false
% 2.76/1.04  
% 2.76/1.04  ------ QBF Options
% 2.76/1.04  
% 2.76/1.04  --qbf_mode                              false
% 2.76/1.04  --qbf_elim_univ                         false
% 2.76/1.04  --qbf_dom_inst                          none
% 2.76/1.04  --qbf_dom_pre_inst                      false
% 2.76/1.04  --qbf_sk_in                             false
% 2.76/1.04  --qbf_pred_elim                         true
% 2.76/1.04  --qbf_split                             512
% 2.76/1.04  
% 2.76/1.04  ------ BMC1 Options
% 2.76/1.04  
% 2.76/1.04  --bmc1_incremental                      false
% 2.76/1.04  --bmc1_axioms                           reachable_all
% 2.76/1.04  --bmc1_min_bound                        0
% 2.76/1.04  --bmc1_max_bound                        -1
% 2.76/1.04  --bmc1_max_bound_default                -1
% 2.76/1.04  --bmc1_symbol_reachability              true
% 2.76/1.04  --bmc1_property_lemmas                  false
% 2.76/1.04  --bmc1_k_induction                      false
% 2.76/1.04  --bmc1_non_equiv_states                 false
% 2.76/1.04  --bmc1_deadlock                         false
% 2.76/1.04  --bmc1_ucm                              false
% 2.76/1.04  --bmc1_add_unsat_core                   none
% 2.76/1.04  --bmc1_unsat_core_children              false
% 2.76/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.04  --bmc1_out_stat                         full
% 2.76/1.04  --bmc1_ground_init                      false
% 2.76/1.04  --bmc1_pre_inst_next_state              false
% 2.76/1.04  --bmc1_pre_inst_state                   false
% 2.76/1.04  --bmc1_pre_inst_reach_state             false
% 2.76/1.04  --bmc1_out_unsat_core                   false
% 2.76/1.04  --bmc1_aig_witness_out                  false
% 2.76/1.04  --bmc1_verbose                          false
% 2.76/1.04  --bmc1_dump_clauses_tptp                false
% 2.76/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.04  --bmc1_dump_file                        -
% 2.76/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.04  --bmc1_ucm_extend_mode                  1
% 2.76/1.04  --bmc1_ucm_init_mode                    2
% 2.76/1.04  --bmc1_ucm_cone_mode                    none
% 2.76/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.04  --bmc1_ucm_relax_model                  4
% 2.76/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.04  --bmc1_ucm_layered_model                none
% 2.76/1.04  --bmc1_ucm_max_lemma_size               10
% 2.76/1.04  
% 2.76/1.04  ------ AIG Options
% 2.76/1.04  
% 2.76/1.04  --aig_mode                              false
% 2.76/1.04  
% 2.76/1.04  ------ Instantiation Options
% 2.76/1.04  
% 2.76/1.04  --instantiation_flag                    true
% 2.76/1.04  --inst_sos_flag                         false
% 2.76/1.04  --inst_sos_phase                        true
% 2.76/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.04  --inst_lit_sel_side                     num_symb
% 2.76/1.04  --inst_solver_per_active                1400
% 2.76/1.04  --inst_solver_calls_frac                1.
% 2.76/1.04  --inst_passive_queue_type               priority_queues
% 2.76/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.04  --inst_passive_queues_freq              [25;2]
% 2.76/1.04  --inst_dismatching                      true
% 2.76/1.04  --inst_eager_unprocessed_to_passive     true
% 2.76/1.04  --inst_prop_sim_given                   true
% 2.76/1.04  --inst_prop_sim_new                     false
% 2.76/1.04  --inst_subs_new                         false
% 2.76/1.04  --inst_eq_res_simp                      false
% 2.76/1.04  --inst_subs_given                       false
% 2.76/1.04  --inst_orphan_elimination               true
% 2.76/1.04  --inst_learning_loop_flag               true
% 2.76/1.04  --inst_learning_start                   3000
% 2.76/1.04  --inst_learning_factor                  2
% 2.76/1.04  --inst_start_prop_sim_after_learn       3
% 2.76/1.04  --inst_sel_renew                        solver
% 2.76/1.04  --inst_lit_activity_flag                true
% 2.76/1.04  --inst_restr_to_given                   false
% 2.76/1.04  --inst_activity_threshold               500
% 2.76/1.04  --inst_out_proof                        true
% 2.76/1.04  
% 2.76/1.04  ------ Resolution Options
% 2.76/1.04  
% 2.76/1.04  --resolution_flag                       true
% 2.76/1.04  --res_lit_sel                           adaptive
% 2.76/1.04  --res_lit_sel_side                      none
% 2.76/1.04  --res_ordering                          kbo
% 2.76/1.04  --res_to_prop_solver                    active
% 2.76/1.04  --res_prop_simpl_new                    false
% 2.76/1.04  --res_prop_simpl_given                  true
% 2.76/1.04  --res_passive_queue_type                priority_queues
% 2.76/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.04  --res_passive_queues_freq               [15;5]
% 2.76/1.04  --res_forward_subs                      full
% 2.76/1.04  --res_backward_subs                     full
% 2.76/1.04  --res_forward_subs_resolution           true
% 2.76/1.04  --res_backward_subs_resolution          true
% 2.76/1.04  --res_orphan_elimination                true
% 2.76/1.04  --res_time_limit                        2.
% 2.76/1.04  --res_out_proof                         true
% 2.76/1.04  
% 2.76/1.04  ------ Superposition Options
% 2.76/1.04  
% 2.76/1.04  --superposition_flag                    true
% 2.76/1.04  --sup_passive_queue_type                priority_queues
% 2.76/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.04  --demod_completeness_check              fast
% 2.76/1.04  --demod_use_ground                      true
% 2.76/1.04  --sup_to_prop_solver                    passive
% 2.76/1.04  --sup_prop_simpl_new                    true
% 2.76/1.04  --sup_prop_simpl_given                  true
% 2.76/1.04  --sup_fun_splitting                     false
% 2.76/1.04  --sup_smt_interval                      50000
% 2.76/1.04  
% 2.76/1.04  ------ Superposition Simplification Setup
% 2.76/1.04  
% 2.76/1.04  --sup_indices_passive                   []
% 2.76/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.04  --sup_full_bw                           [BwDemod]
% 2.76/1.04  --sup_immed_triv                        [TrivRules]
% 2.76/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.04  --sup_immed_bw_main                     []
% 2.76/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.04  
% 2.76/1.04  ------ Combination Options
% 2.76/1.04  
% 2.76/1.04  --comb_res_mult                         3
% 2.76/1.04  --comb_sup_mult                         2
% 2.76/1.04  --comb_inst_mult                        10
% 2.76/1.04  
% 2.76/1.04  ------ Debug Options
% 2.76/1.04  
% 2.76/1.04  --dbg_backtrace                         false
% 2.76/1.04  --dbg_dump_prop_clauses                 false
% 2.76/1.04  --dbg_dump_prop_clauses_file            -
% 2.76/1.04  --dbg_out_stat                          false
% 2.76/1.04  ------ Parsing...
% 2.76/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/1.04  
% 2.76/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.76/1.04  
% 2.76/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/1.04  
% 2.76/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/1.04  ------ Proving...
% 2.76/1.04  ------ Problem Properties 
% 2.76/1.04  
% 2.76/1.04  
% 2.76/1.04  clauses                                 20
% 2.76/1.04  conjectures                             2
% 2.76/1.04  EPR                                     1
% 2.76/1.04  Horn                                    17
% 2.76/1.04  unary                                   6
% 2.76/1.04  binary                                  5
% 2.76/1.04  lits                                    45
% 2.76/1.04  lits eq                                 28
% 2.76/1.04  fd_pure                                 0
% 2.76/1.04  fd_pseudo                               0
% 2.76/1.04  fd_cond                                 0
% 2.76/1.04  fd_pseudo_cond                          3
% 2.76/1.04  AC symbols                              0
% 2.76/1.04  
% 2.76/1.04  ------ Schedule dynamic 5 is on 
% 2.76/1.04  
% 2.76/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/1.04  
% 2.76/1.04  
% 2.76/1.04  ------ 
% 2.76/1.04  Current options:
% 2.76/1.04  ------ 
% 2.76/1.04  
% 2.76/1.04  ------ Input Options
% 2.76/1.04  
% 2.76/1.04  --out_options                           all
% 2.76/1.04  --tptp_safe_out                         true
% 2.76/1.04  --problem_path                          ""
% 2.76/1.04  --include_path                          ""
% 2.76/1.04  --clausifier                            res/vclausify_rel
% 2.76/1.04  --clausifier_options                    --mode clausify
% 2.76/1.04  --stdin                                 false
% 2.76/1.04  --stats_out                             all
% 2.76/1.04  
% 2.76/1.04  ------ General Options
% 2.76/1.04  
% 2.76/1.04  --fof                                   false
% 2.76/1.04  --time_out_real                         305.
% 2.76/1.04  --time_out_virtual                      -1.
% 2.76/1.04  --symbol_type_check                     false
% 2.76/1.04  --clausify_out                          false
% 2.76/1.04  --sig_cnt_out                           false
% 2.76/1.04  --trig_cnt_out                          false
% 2.76/1.04  --trig_cnt_out_tolerance                1.
% 2.76/1.04  --trig_cnt_out_sk_spl                   false
% 2.76/1.04  --abstr_cl_out                          false
% 2.76/1.04  
% 2.76/1.04  ------ Global Options
% 2.76/1.04  
% 2.76/1.04  --schedule                              default
% 2.76/1.04  --add_important_lit                     false
% 2.76/1.04  --prop_solver_per_cl                    1000
% 2.76/1.04  --min_unsat_core                        false
% 2.76/1.04  --soft_assumptions                      false
% 2.76/1.04  --soft_lemma_size                       3
% 2.76/1.04  --prop_impl_unit_size                   0
% 2.76/1.04  --prop_impl_unit                        []
% 2.76/1.04  --share_sel_clauses                     true
% 2.76/1.04  --reset_solvers                         false
% 2.76/1.04  --bc_imp_inh                            [conj_cone]
% 2.76/1.04  --conj_cone_tolerance                   3.
% 2.76/1.04  --extra_neg_conj                        none
% 2.76/1.04  --large_theory_mode                     true
% 2.76/1.04  --prolific_symb_bound                   200
% 2.76/1.04  --lt_threshold                          2000
% 2.76/1.04  --clause_weak_htbl                      true
% 2.76/1.04  --gc_record_bc_elim                     false
% 2.76/1.04  
% 2.76/1.04  ------ Preprocessing Options
% 2.76/1.04  
% 2.76/1.04  --preprocessing_flag                    true
% 2.76/1.04  --time_out_prep_mult                    0.1
% 2.76/1.04  --splitting_mode                        input
% 2.76/1.04  --splitting_grd                         true
% 2.76/1.04  --splitting_cvd                         false
% 2.76/1.04  --splitting_cvd_svl                     false
% 2.76/1.04  --splitting_nvd                         32
% 2.76/1.04  --sub_typing                            true
% 2.76/1.04  --prep_gs_sim                           true
% 2.76/1.04  --prep_unflatten                        true
% 2.76/1.04  --prep_res_sim                          true
% 2.76/1.04  --prep_upred                            true
% 2.76/1.04  --prep_sem_filter                       exhaustive
% 2.76/1.04  --prep_sem_filter_out                   false
% 2.76/1.04  --pred_elim                             true
% 2.76/1.04  --res_sim_input                         true
% 2.76/1.04  --eq_ax_congr_red                       true
% 2.76/1.04  --pure_diseq_elim                       true
% 2.76/1.04  --brand_transform                       false
% 2.76/1.04  --non_eq_to_eq                          false
% 2.76/1.04  --prep_def_merge                        true
% 2.76/1.04  --prep_def_merge_prop_impl              false
% 2.76/1.04  --prep_def_merge_mbd                    true
% 2.76/1.04  --prep_def_merge_tr_red                 false
% 2.76/1.04  --prep_def_merge_tr_cl                  false
% 2.76/1.04  --smt_preprocessing                     true
% 2.76/1.04  --smt_ac_axioms                         fast
% 2.76/1.04  --preprocessed_out                      false
% 2.76/1.04  --preprocessed_stats                    false
% 2.76/1.04  
% 2.76/1.04  ------ Abstraction refinement Options
% 2.76/1.04  
% 2.76/1.04  --abstr_ref                             []
% 2.76/1.04  --abstr_ref_prep                        false
% 2.76/1.04  --abstr_ref_until_sat                   false
% 2.76/1.04  --abstr_ref_sig_restrict                funpre
% 2.76/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/1.04  --abstr_ref_under                       []
% 2.76/1.04  
% 2.76/1.04  ------ SAT Options
% 2.76/1.04  
% 2.76/1.04  --sat_mode                              false
% 2.76/1.04  --sat_fm_restart_options                ""
% 2.76/1.04  --sat_gr_def                            false
% 2.76/1.04  --sat_epr_types                         true
% 2.76/1.04  --sat_non_cyclic_types                  false
% 2.76/1.04  --sat_finite_models                     false
% 2.76/1.04  --sat_fm_lemmas                         false
% 2.76/1.04  --sat_fm_prep                           false
% 2.76/1.04  --sat_fm_uc_incr                        true
% 2.76/1.04  --sat_out_model                         small
% 2.76/1.04  --sat_out_clauses                       false
% 2.76/1.04  
% 2.76/1.04  ------ QBF Options
% 2.76/1.04  
% 2.76/1.04  --qbf_mode                              false
% 2.76/1.04  --qbf_elim_univ                         false
% 2.76/1.04  --qbf_dom_inst                          none
% 2.76/1.04  --qbf_dom_pre_inst                      false
% 2.76/1.04  --qbf_sk_in                             false
% 2.76/1.04  --qbf_pred_elim                         true
% 2.76/1.04  --qbf_split                             512
% 2.76/1.04  
% 2.76/1.04  ------ BMC1 Options
% 2.76/1.04  
% 2.76/1.04  --bmc1_incremental                      false
% 2.76/1.04  --bmc1_axioms                           reachable_all
% 2.76/1.04  --bmc1_min_bound                        0
% 2.76/1.04  --bmc1_max_bound                        -1
% 2.76/1.04  --bmc1_max_bound_default                -1
% 2.76/1.04  --bmc1_symbol_reachability              true
% 2.76/1.04  --bmc1_property_lemmas                  false
% 2.76/1.04  --bmc1_k_induction                      false
% 2.76/1.04  --bmc1_non_equiv_states                 false
% 2.76/1.04  --bmc1_deadlock                         false
% 2.76/1.04  --bmc1_ucm                              false
% 2.76/1.04  --bmc1_add_unsat_core                   none
% 2.76/1.04  --bmc1_unsat_core_children              false
% 2.76/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/1.04  --bmc1_out_stat                         full
% 2.76/1.04  --bmc1_ground_init                      false
% 2.76/1.04  --bmc1_pre_inst_next_state              false
% 2.76/1.04  --bmc1_pre_inst_state                   false
% 2.76/1.04  --bmc1_pre_inst_reach_state             false
% 2.76/1.04  --bmc1_out_unsat_core                   false
% 2.76/1.04  --bmc1_aig_witness_out                  false
% 2.76/1.04  --bmc1_verbose                          false
% 2.76/1.04  --bmc1_dump_clauses_tptp                false
% 2.76/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.76/1.04  --bmc1_dump_file                        -
% 2.76/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.76/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.76/1.04  --bmc1_ucm_extend_mode                  1
% 2.76/1.04  --bmc1_ucm_init_mode                    2
% 2.76/1.04  --bmc1_ucm_cone_mode                    none
% 2.76/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.76/1.04  --bmc1_ucm_relax_model                  4
% 2.76/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.76/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/1.04  --bmc1_ucm_layered_model                none
% 2.76/1.04  --bmc1_ucm_max_lemma_size               10
% 2.76/1.04  
% 2.76/1.04  ------ AIG Options
% 2.76/1.04  
% 2.76/1.04  --aig_mode                              false
% 2.76/1.04  
% 2.76/1.04  ------ Instantiation Options
% 2.76/1.04  
% 2.76/1.04  --instantiation_flag                    true
% 2.76/1.04  --inst_sos_flag                         false
% 2.76/1.04  --inst_sos_phase                        true
% 2.76/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/1.04  --inst_lit_sel_side                     none
% 2.76/1.04  --inst_solver_per_active                1400
% 2.76/1.04  --inst_solver_calls_frac                1.
% 2.76/1.04  --inst_passive_queue_type               priority_queues
% 2.76/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/1.04  --inst_passive_queues_freq              [25;2]
% 2.76/1.04  --inst_dismatching                      true
% 2.76/1.04  --inst_eager_unprocessed_to_passive     true
% 2.76/1.04  --inst_prop_sim_given                   true
% 2.76/1.04  --inst_prop_sim_new                     false
% 2.76/1.04  --inst_subs_new                         false
% 2.76/1.04  --inst_eq_res_simp                      false
% 2.76/1.04  --inst_subs_given                       false
% 2.76/1.04  --inst_orphan_elimination               true
% 2.76/1.04  --inst_learning_loop_flag               true
% 2.76/1.04  --inst_learning_start                   3000
% 2.76/1.04  --inst_learning_factor                  2
% 2.76/1.04  --inst_start_prop_sim_after_learn       3
% 2.76/1.04  --inst_sel_renew                        solver
% 2.76/1.04  --inst_lit_activity_flag                true
% 2.76/1.04  --inst_restr_to_given                   false
% 2.76/1.04  --inst_activity_threshold               500
% 2.76/1.04  --inst_out_proof                        true
% 2.76/1.04  
% 2.76/1.04  ------ Resolution Options
% 2.76/1.04  
% 2.76/1.04  --resolution_flag                       false
% 2.76/1.04  --res_lit_sel                           adaptive
% 2.76/1.04  --res_lit_sel_side                      none
% 2.76/1.04  --res_ordering                          kbo
% 2.76/1.04  --res_to_prop_solver                    active
% 2.76/1.04  --res_prop_simpl_new                    false
% 2.76/1.04  --res_prop_simpl_given                  true
% 2.76/1.04  --res_passive_queue_type                priority_queues
% 2.76/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/1.04  --res_passive_queues_freq               [15;5]
% 2.76/1.04  --res_forward_subs                      full
% 2.76/1.04  --res_backward_subs                     full
% 2.76/1.04  --res_forward_subs_resolution           true
% 2.76/1.04  --res_backward_subs_resolution          true
% 2.76/1.04  --res_orphan_elimination                true
% 2.76/1.04  --res_time_limit                        2.
% 2.76/1.04  --res_out_proof                         true
% 2.76/1.04  
% 2.76/1.04  ------ Superposition Options
% 2.76/1.04  
% 2.76/1.04  --superposition_flag                    true
% 2.76/1.04  --sup_passive_queue_type                priority_queues
% 2.76/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.76/1.04  --demod_completeness_check              fast
% 2.76/1.04  --demod_use_ground                      true
% 2.76/1.04  --sup_to_prop_solver                    passive
% 2.76/1.04  --sup_prop_simpl_new                    true
% 2.76/1.04  --sup_prop_simpl_given                  true
% 2.76/1.04  --sup_fun_splitting                     false
% 2.76/1.04  --sup_smt_interval                      50000
% 2.76/1.04  
% 2.76/1.04  ------ Superposition Simplification Setup
% 2.76/1.04  
% 2.76/1.04  --sup_indices_passive                   []
% 2.76/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.04  --sup_full_bw                           [BwDemod]
% 2.76/1.04  --sup_immed_triv                        [TrivRules]
% 2.76/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.04  --sup_immed_bw_main                     []
% 2.76/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/1.04  
% 2.76/1.04  ------ Combination Options
% 2.76/1.04  
% 2.76/1.04  --comb_res_mult                         3
% 2.76/1.04  --comb_sup_mult                         2
% 2.76/1.04  --comb_inst_mult                        10
% 2.76/1.04  
% 2.76/1.04  ------ Debug Options
% 2.76/1.04  
% 2.76/1.04  --dbg_backtrace                         false
% 2.76/1.04  --dbg_dump_prop_clauses                 false
% 2.76/1.04  --dbg_dump_prop_clauses_file            -
% 2.76/1.04  --dbg_out_stat                          false
% 2.76/1.04  
% 2.76/1.04  
% 2.76/1.04  
% 2.76/1.04  
% 2.76/1.04  ------ Proving...
% 2.76/1.04  
% 2.76/1.04  
% 2.76/1.04  % SZS status Theorem for theBenchmark.p
% 2.76/1.04  
% 2.76/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/1.04  
% 2.76/1.04  fof(f8,axiom,(
% 2.76/1.04    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f21,plain,(
% 2.76/1.04    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.76/1.04    inference(ennf_transformation,[],[f8])).
% 2.76/1.04  
% 2.76/1.04  fof(f54,plain,(
% 2.76/1.04    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f21])).
% 2.76/1.04  
% 2.76/1.04  fof(f16,conjecture,(
% 2.76/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f17,negated_conjecture,(
% 2.76/1.04    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.76/1.04    inference(negated_conjecture,[],[f16])).
% 2.76/1.04  
% 2.76/1.04  fof(f32,plain,(
% 2.76/1.04    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.76/1.04    inference(ennf_transformation,[],[f17])).
% 2.76/1.04  
% 2.76/1.04  fof(f33,plain,(
% 2.76/1.04    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.76/1.04    inference(flattening,[],[f32])).
% 2.76/1.04  
% 2.76/1.04  fof(f40,plain,(
% 2.76/1.04    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 2.76/1.04    introduced(choice_axiom,[])).
% 2.76/1.04  
% 2.76/1.04  fof(f41,plain,(
% 2.76/1.04    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 2.76/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f33,f40])).
% 2.76/1.04  
% 2.76/1.04  fof(f68,plain,(
% 2.76/1.04    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 2.76/1.04    inference(cnf_transformation,[],[f41])).
% 2.76/1.04  
% 2.76/1.04  fof(f2,axiom,(
% 2.76/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f48,plain,(
% 2.76/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f2])).
% 2.76/1.04  
% 2.76/1.04  fof(f3,axiom,(
% 2.76/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f49,plain,(
% 2.76/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f3])).
% 2.76/1.04  
% 2.76/1.04  fof(f4,axiom,(
% 2.76/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f50,plain,(
% 2.76/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f4])).
% 2.76/1.04  
% 2.76/1.04  fof(f72,plain,(
% 2.76/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.76/1.04    inference(definition_unfolding,[],[f49,f50])).
% 2.76/1.04  
% 2.76/1.04  fof(f73,plain,(
% 2.76/1.04    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.76/1.04    inference(definition_unfolding,[],[f48,f72])).
% 2.76/1.04  
% 2.76/1.04  fof(f84,plain,(
% 2.76/1.04    v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 2.76/1.04    inference(definition_unfolding,[],[f68,f73])).
% 2.76/1.04  
% 2.76/1.04  fof(f15,axiom,(
% 2.76/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f30,plain,(
% 2.76/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.04    inference(ennf_transformation,[],[f15])).
% 2.76/1.04  
% 2.76/1.04  fof(f31,plain,(
% 2.76/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.04    inference(flattening,[],[f30])).
% 2.76/1.04  
% 2.76/1.04  fof(f39,plain,(
% 2.76/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.04    inference(nnf_transformation,[],[f31])).
% 2.76/1.04  
% 2.76/1.04  fof(f61,plain,(
% 2.76/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.04    inference(cnf_transformation,[],[f39])).
% 2.76/1.04  
% 2.76/1.04  fof(f69,plain,(
% 2.76/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.76/1.04    inference(cnf_transformation,[],[f41])).
% 2.76/1.04  
% 2.76/1.04  fof(f83,plain,(
% 2.76/1.04    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 2.76/1.04    inference(definition_unfolding,[],[f69,f73])).
% 2.76/1.04  
% 2.76/1.04  fof(f70,plain,(
% 2.76/1.04    k1_xboole_0 != sK2),
% 2.76/1.04    inference(cnf_transformation,[],[f41])).
% 2.76/1.04  
% 2.76/1.04  fof(f13,axiom,(
% 2.76/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f28,plain,(
% 2.76/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.04    inference(ennf_transformation,[],[f13])).
% 2.76/1.04  
% 2.76/1.04  fof(f59,plain,(
% 2.76/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.04    inference(cnf_transformation,[],[f28])).
% 2.76/1.04  
% 2.76/1.04  fof(f5,axiom,(
% 2.76/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f19,plain,(
% 2.76/1.04    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.76/1.04    inference(ennf_transformation,[],[f5])).
% 2.76/1.04  
% 2.76/1.04  fof(f51,plain,(
% 2.76/1.04    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f19])).
% 2.76/1.04  
% 2.76/1.04  fof(f7,axiom,(
% 2.76/1.04    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f53,plain,(
% 2.76/1.04    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.76/1.04    inference(cnf_transformation,[],[f7])).
% 2.76/1.04  
% 2.76/1.04  fof(f6,axiom,(
% 2.76/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f20,plain,(
% 2.76/1.04    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.76/1.04    inference(ennf_transformation,[],[f6])).
% 2.76/1.04  
% 2.76/1.04  fof(f52,plain,(
% 2.76/1.04    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f20])).
% 2.76/1.04  
% 2.76/1.04  fof(f80,plain,(
% 2.76/1.04    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.76/1.04    inference(definition_unfolding,[],[f52,f73])).
% 2.76/1.04  
% 2.76/1.04  fof(f12,axiom,(
% 2.76/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f18,plain,(
% 2.76/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.76/1.04    inference(pure_predicate_removal,[],[f12])).
% 2.76/1.04  
% 2.76/1.04  fof(f27,plain,(
% 2.76/1.04    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.04    inference(ennf_transformation,[],[f18])).
% 2.76/1.04  
% 2.76/1.04  fof(f58,plain,(
% 2.76/1.04    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.04    inference(cnf_transformation,[],[f27])).
% 2.76/1.04  
% 2.76/1.04  fof(f10,axiom,(
% 2.76/1.04    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f23,plain,(
% 2.76/1.04    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.76/1.04    inference(ennf_transformation,[],[f10])).
% 2.76/1.04  
% 2.76/1.04  fof(f24,plain,(
% 2.76/1.04    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/1.04    inference(flattening,[],[f23])).
% 2.76/1.04  
% 2.76/1.04  fof(f56,plain,(
% 2.76/1.04    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f24])).
% 2.76/1.04  
% 2.76/1.04  fof(f9,axiom,(
% 2.76/1.04    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f22,plain,(
% 2.76/1.04    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.76/1.04    inference(ennf_transformation,[],[f9])).
% 2.76/1.04  
% 2.76/1.04  fof(f55,plain,(
% 2.76/1.04    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f22])).
% 2.76/1.04  
% 2.76/1.04  fof(f1,axiom,(
% 2.76/1.04    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f34,plain,(
% 2.76/1.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.76/1.04    inference(nnf_transformation,[],[f1])).
% 2.76/1.04  
% 2.76/1.04  fof(f35,plain,(
% 2.76/1.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.76/1.04    inference(flattening,[],[f34])).
% 2.76/1.04  
% 2.76/1.04  fof(f36,plain,(
% 2.76/1.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.76/1.04    inference(rectify,[],[f35])).
% 2.76/1.04  
% 2.76/1.04  fof(f37,plain,(
% 2.76/1.04    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.76/1.04    introduced(choice_axiom,[])).
% 2.76/1.04  
% 2.76/1.04  fof(f38,plain,(
% 2.76/1.04    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.76/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 2.76/1.04  
% 2.76/1.04  fof(f43,plain,(
% 2.76/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.76/1.04    inference(cnf_transformation,[],[f38])).
% 2.76/1.04  
% 2.76/1.04  fof(f78,plain,(
% 2.76/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.76/1.04    inference(definition_unfolding,[],[f43,f72])).
% 2.76/1.04  
% 2.76/1.04  fof(f87,plain,(
% 2.76/1.04    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 2.76/1.04    inference(equality_resolution,[],[f78])).
% 2.76/1.04  
% 2.76/1.04  fof(f88,plain,(
% 2.76/1.04    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 2.76/1.04    inference(equality_resolution,[],[f87])).
% 2.76/1.04  
% 2.76/1.04  fof(f11,axiom,(
% 2.76/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f25,plain,(
% 2.76/1.04    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.76/1.04    inference(ennf_transformation,[],[f11])).
% 2.76/1.04  
% 2.76/1.04  fof(f26,plain,(
% 2.76/1.04    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.76/1.04    inference(flattening,[],[f25])).
% 2.76/1.04  
% 2.76/1.04  fof(f57,plain,(
% 2.76/1.04    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.76/1.04    inference(cnf_transformation,[],[f26])).
% 2.76/1.04  
% 2.76/1.04  fof(f81,plain,(
% 2.76/1.04    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.76/1.04    inference(definition_unfolding,[],[f57,f73])).
% 2.76/1.04  
% 2.76/1.04  fof(f67,plain,(
% 2.76/1.04    v1_funct_1(sK4)),
% 2.76/1.04    inference(cnf_transformation,[],[f41])).
% 2.76/1.04  
% 2.76/1.04  fof(f14,axiom,(
% 2.76/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.76/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/1.04  
% 2.76/1.04  fof(f29,plain,(
% 2.76/1.04    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/1.04    inference(ennf_transformation,[],[f14])).
% 2.76/1.04  
% 2.76/1.04  fof(f60,plain,(
% 2.76/1.04    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/1.04    inference(cnf_transformation,[],[f29])).
% 2.76/1.04  
% 2.76/1.04  fof(f71,plain,(
% 2.76/1.04    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 2.76/1.04    inference(cnf_transformation,[],[f41])).
% 2.76/1.04  
% 2.76/1.04  fof(f82,plain,(
% 2.76/1.04    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 2.76/1.04    inference(definition_unfolding,[],[f71,f73,f73])).
% 2.76/1.04  
% 2.76/1.04  cnf(c_9,plain,
% 2.76/1.04      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.76/1.04      inference(cnf_transformation,[],[f54]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1333,plain,
% 2.76/1.04      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 2.76/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_25,negated_conjecture,
% 2.76/1.04      ( v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 2.76/1.04      inference(cnf_transformation,[],[f84]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_21,plain,
% 2.76/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.76/1.04      | k1_xboole_0 = X2 ),
% 2.76/1.04      inference(cnf_transformation,[],[f61]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_24,negated_conjecture,
% 2.76/1.04      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 2.76/1.04      inference(cnf_transformation,[],[f83]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_380,plain,
% 2.76/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 2.76/1.04      | k1_relset_1(X1,X2,X0) = X1
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.76/1.04      | sK4 != X0
% 2.76/1.04      | k1_xboole_0 = X2 ),
% 2.76/1.04      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_381,plain,
% 2.76/1.04      ( ~ v1_funct_2(sK4,X0,X1)
% 2.76/1.04      | k1_relset_1(X0,X1,sK4) = X0
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.76/1.04      | k1_xboole_0 = X1 ),
% 2.76/1.04      inference(unflattening,[status(thm)],[c_380]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_718,plain,
% 2.76/1.04      ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
% 2.76/1.04      | k1_relset_1(X0,X1,sK4) = X0
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.76/1.04      | sK4 != sK4
% 2.76/1.04      | sK2 != X1
% 2.76/1.04      | k1_xboole_0 = X1 ),
% 2.76/1.04      inference(resolution_lifted,[status(thm)],[c_25,c_381]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_719,plain,
% 2.76/1.04      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.76/1.04      | k1_xboole_0 = sK2 ),
% 2.76/1.04      inference(unflattening,[status(thm)],[c_718]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_23,negated_conjecture,
% 2.76/1.04      ( k1_xboole_0 != sK2 ),
% 2.76/1.04      inference(cnf_transformation,[],[f70]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_720,plain,
% 2.76/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.76/1.04      | k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 2.76/1.04      inference(global_propositional_subsumption,
% 2.76/1.04                [status(thm)],
% 2.76/1.04                [c_719,c_23]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_721,plain,
% 2.76/1.04      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.76/1.04      inference(renaming,[status(thm)],[c_720]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_784,plain,
% 2.76/1.04      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 2.76/1.04      inference(equality_resolution_simp,[status(thm)],[c_721]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_14,plain,
% 2.76/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.76/1.04      inference(cnf_transformation,[],[f59]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_425,plain,
% 2.76/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.76/1.04      | sK4 != X2 ),
% 2.76/1.04      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_426,plain,
% 2.76/1.04      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.76/1.04      inference(unflattening,[status(thm)],[c_425]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1466,plain,
% 2.76/1.04      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
% 2.76/1.04      inference(equality_resolution,[status(thm)],[c_426]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1583,plain,
% 2.76/1.04      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 2.76/1.04      inference(light_normalisation,[status(thm)],[c_784,c_1466]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_6,plain,
% 2.76/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/1.04      | ~ v1_relat_1(X1)
% 2.76/1.04      | v1_relat_1(X0) ),
% 2.76/1.04      inference(cnf_transformation,[],[f51]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_350,plain,
% 2.76/1.04      ( ~ v1_relat_1(X0)
% 2.76/1.04      | v1_relat_1(X1)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 2.76/1.04      | sK4 != X1 ),
% 2.76/1.04      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_351,plain,
% 2.76/1.04      ( ~ v1_relat_1(X0)
% 2.76/1.04      | v1_relat_1(sK4)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0) ),
% 2.76/1.04      inference(unflattening,[status(thm)],[c_350]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1329,plain,
% 2.76/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(X0)
% 2.76/1.04      | v1_relat_1(X0) != iProver_top
% 2.76/1.04      | v1_relat_1(sK4) = iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1055,plain,( X0 = X0 ),theory(equality) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1472,plain,
% 2.76/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.76/1.04      inference(instantiation,[status(thm)],[c_1055]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1467,plain,
% 2.76/1.04      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.76/1.04      | v1_relat_1(sK4)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.76/1.04      inference(instantiation,[status(thm)],[c_351]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1580,plain,
% 2.76/1.04      ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.76/1.04      | v1_relat_1(sK4)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.76/1.04      inference(instantiation,[status(thm)],[c_1467]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1581,plain,
% 2.76/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.76/1.04      | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top
% 2.76/1.04      | v1_relat_1(sK4) = iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_1580]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_8,plain,
% 2.76/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.76/1.04      inference(cnf_transformation,[],[f53]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1714,plain,
% 2.76/1.04      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.76/1.04      inference(instantiation,[status(thm)],[c_8]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1715,plain,
% 2.76/1.04      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1948,plain,
% 2.76/1.04      ( v1_relat_1(sK4) = iProver_top ),
% 2.76/1.04      inference(global_propositional_subsumption,
% 2.76/1.04                [status(thm)],
% 2.76/1.04                [c_1329,c_1472,c_1581,c_1715]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_7,plain,
% 2.76/1.04      ( ~ v1_relat_1(X0)
% 2.76/1.04      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.76/1.04      inference(cnf_transformation,[],[f80]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1335,plain,
% 2.76/1.04      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.76/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2183,plain,
% 2.76/1.04      ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 2.76/1.04      inference(superposition,[status(thm)],[c_1948,c_1335]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2669,plain,
% 2.76/1.04      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
% 2.76/1.04      inference(superposition,[status(thm)],[c_1583,c_2183]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_13,plain,
% 2.76/1.04      ( v4_relat_1(X0,X1)
% 2.76/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.76/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_11,plain,
% 2.76/1.04      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.76/1.04      inference(cnf_transformation,[],[f56]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_313,plain,
% 2.76/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.04      | ~ v1_relat_1(X0)
% 2.76/1.04      | k7_relat_1(X0,X1) = X0 ),
% 2.76/1.04      inference(resolution,[status(thm)],[c_13,c_11]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_365,plain,
% 2.76/1.04      ( ~ v1_relat_1(X0)
% 2.76/1.04      | k7_relat_1(X0,X1) = X0
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.76/1.04      | sK4 != X0 ),
% 2.76/1.04      inference(resolution_lifted,[status(thm)],[c_313,c_24]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_366,plain,
% 2.76/1.04      ( ~ v1_relat_1(sK4)
% 2.76/1.04      | k7_relat_1(sK4,X0) = sK4
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.76/1.04      inference(unflattening,[status(thm)],[c_365]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1328,plain,
% 2.76/1.04      ( k7_relat_1(sK4,X0) = sK4
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.76/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2020,plain,
% 2.76/1.04      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.76/1.04      | k7_relat_1(sK4,X0) = sK4 ),
% 2.76/1.04      inference(global_propositional_subsumption,
% 2.76/1.04                [status(thm)],
% 2.76/1.04                [c_1328,c_366,c_1472,c_1580,c_1714]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2021,plain,
% 2.76/1.04      ( k7_relat_1(sK4,X0) = sK4
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.76/1.04      inference(renaming,[status(thm)],[c_2020]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2023,plain,
% 2.76/1.04      ( k7_relat_1(sK4,X0) = sK4
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.76/1.04      inference(light_normalisation,[status(thm)],[c_2021,c_1583]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2027,plain,
% 2.76/1.04      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
% 2.76/1.04      inference(equality_resolution,[status(thm)],[c_2023]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_10,plain,
% 2.76/1.04      ( ~ v1_relat_1(X0)
% 2.76/1.04      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.76/1.04      inference(cnf_transformation,[],[f55]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1332,plain,
% 2.76/1.04      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.76/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1953,plain,
% 2.76/1.04      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 2.76/1.04      inference(superposition,[status(thm)],[c_1948,c_1332]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_3286,plain,
% 2.76/1.04      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 2.76/1.04      inference(superposition,[status(thm)],[c_2027,c_1953]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_3911,plain,
% 2.76/1.04      ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 2.76/1.04      inference(light_normalisation,[status(thm)],[c_2669,c_3286]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_4,plain,
% 2.76/1.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 2.76/1.04      inference(cnf_transformation,[],[f88]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1337,plain,
% 2.76/1.04      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1703,plain,
% 2.76/1.04      ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.76/1.04      inference(superposition,[status(thm)],[c_1583,c_1337]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_12,plain,
% 2.76/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.76/1.04      | ~ v1_funct_1(X1)
% 2.76/1.04      | ~ v1_relat_1(X1)
% 2.76/1.04      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 2.76/1.04      inference(cnf_transformation,[],[f81]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_26,negated_conjecture,
% 2.76/1.04      ( v1_funct_1(sK4) ),
% 2.76/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_331,plain,
% 2.76/1.04      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.76/1.04      | ~ v1_relat_1(X1)
% 2.76/1.04      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 2.76/1.04      | sK4 != X1 ),
% 2.76/1.04      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_332,plain,
% 2.76/1.04      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.76/1.04      | ~ v1_relat_1(sK4)
% 2.76/1.04      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 2.76/1.04      inference(unflattening,[status(thm)],[c_331]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1330,plain,
% 2.76/1.04      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.76/1.04      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.76/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_333,plain,
% 2.76/1.04      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.76/1.04      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.76/1.04      | v1_relat_1(sK4) != iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2029,plain,
% 2.76/1.04      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.76/1.04      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 2.76/1.04      inference(global_propositional_subsumption,
% 2.76/1.04                [status(thm)],
% 2.76/1.04                [c_1330,c_333,c_1472,c_1581,c_1715]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2030,plain,
% 2.76/1.04      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.76/1.04      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.76/1.04      inference(renaming,[status(thm)],[c_2029]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2682,plain,
% 2.76/1.04      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
% 2.76/1.04      inference(superposition,[status(thm)],[c_1703,c_2030]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_15,plain,
% 2.76/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/1.04      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.76/1.04      inference(cnf_transformation,[],[f60]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_416,plain,
% 2.76/1.04      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.76/1.04      | sK4 != X2 ),
% 2.76/1.04      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_417,plain,
% 2.76/1.04      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 2.76/1.04      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.76/1.04      inference(unflattening,[status(thm)],[c_416]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1495,plain,
% 2.76/1.04      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.76/1.04      inference(equality_resolution,[status(thm)],[c_417]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_22,negated_conjecture,
% 2.76/1.04      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 2.76/1.04      inference(cnf_transformation,[],[f82]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1331,plain,
% 2.76/1.04      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.76/1.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_1561,plain,
% 2.76/1.04      ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.76/1.04      inference(demodulation,[status(thm)],[c_1495,c_1331]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_2903,plain,
% 2.76/1.04      ( r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) != iProver_top ),
% 2.76/1.04      inference(demodulation,[status(thm)],[c_2682,c_1561]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_3914,plain,
% 2.76/1.04      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 2.76/1.04      inference(demodulation,[status(thm)],[c_3911,c_2903]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(c_3926,plain,
% 2.76/1.04      ( v1_relat_1(sK4) != iProver_top ),
% 2.76/1.04      inference(superposition,[status(thm)],[c_1333,c_3914]) ).
% 2.76/1.04  
% 2.76/1.04  cnf(contradiction,plain,
% 2.76/1.04      ( $false ),
% 2.76/1.04      inference(minisat,[status(thm)],[c_3926,c_1715,c_1581,c_1472]) ).
% 2.76/1.04  
% 2.76/1.04  
% 2.76/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/1.04  
% 2.76/1.04  ------                               Statistics
% 2.76/1.04  
% 2.76/1.04  ------ General
% 2.76/1.04  
% 2.76/1.04  abstr_ref_over_cycles:                  0
% 2.76/1.04  abstr_ref_under_cycles:                 0
% 2.76/1.04  gc_basic_clause_elim:                   0
% 2.76/1.04  forced_gc_time:                         0
% 2.76/1.04  parsing_time:                           0.007
% 2.76/1.04  unif_index_cands_time:                  0.
% 2.76/1.04  unif_index_add_time:                    0.
% 2.76/1.04  orderings_time:                         0.
% 2.76/1.04  out_proof_time:                         0.007
% 2.76/1.04  total_time:                             0.119
% 2.76/1.04  num_of_symbols:                         55
% 2.76/1.04  num_of_terms:                           5096
% 2.76/1.04  
% 2.76/1.04  ------ Preprocessing
% 2.76/1.04  
% 2.76/1.04  num_of_splits:                          0
% 2.76/1.04  num_of_split_atoms:                     0
% 2.76/1.04  num_of_reused_defs:                     0
% 2.76/1.04  num_eq_ax_congr_red:                    23
% 2.76/1.04  num_of_sem_filtered_clauses:            1
% 2.76/1.04  num_of_subtypes:                        0
% 2.76/1.04  monotx_restored_types:                  0
% 2.76/1.04  sat_num_of_epr_types:                   0
% 2.76/1.04  sat_num_of_non_cyclic_types:            0
% 2.76/1.04  sat_guarded_non_collapsed_types:        0
% 2.76/1.04  num_pure_diseq_elim:                    0
% 2.76/1.04  simp_replaced_by:                       0
% 2.76/1.04  res_preprocessed:                       120
% 2.76/1.04  prep_upred:                             0
% 2.76/1.04  prep_unflattend:                        51
% 2.76/1.04  smt_new_axioms:                         0
% 2.76/1.04  pred_elim_cands:                        3
% 2.76/1.04  pred_elim:                              4
% 2.76/1.04  pred_elim_cl:                           7
% 2.76/1.04  pred_elim_cycles:                       9
% 2.76/1.04  merged_defs:                            0
% 2.76/1.04  merged_defs_ncl:                        0
% 2.76/1.04  bin_hyper_res:                          0
% 2.76/1.04  prep_cycles:                            4
% 2.76/1.04  pred_elim_time:                         0.01
% 2.76/1.04  splitting_time:                         0.
% 2.76/1.04  sem_filter_time:                        0.
% 2.76/1.04  monotx_time:                            0.
% 2.76/1.04  subtype_inf_time:                       0.
% 2.76/1.04  
% 2.76/1.04  ------ Problem properties
% 2.76/1.04  
% 2.76/1.04  clauses:                                20
% 2.76/1.04  conjectures:                            2
% 2.76/1.04  epr:                                    1
% 2.76/1.04  horn:                                   17
% 2.76/1.04  ground:                                 5
% 2.76/1.04  unary:                                  6
% 2.76/1.04  binary:                                 5
% 2.76/1.04  lits:                                   45
% 2.76/1.04  lits_eq:                                28
% 2.76/1.04  fd_pure:                                0
% 2.76/1.04  fd_pseudo:                              0
% 2.76/1.04  fd_cond:                                0
% 2.76/1.04  fd_pseudo_cond:                         3
% 2.76/1.04  ac_symbols:                             0
% 2.76/1.04  
% 2.76/1.04  ------ Propositional Solver
% 2.76/1.04  
% 2.76/1.04  prop_solver_calls:                      27
% 2.76/1.04  prop_fast_solver_calls:                 803
% 2.76/1.04  smt_solver_calls:                       0
% 2.76/1.04  smt_fast_solver_calls:                  0
% 2.76/1.04  prop_num_of_clauses:                    1359
% 2.76/1.04  prop_preprocess_simplified:             5134
% 2.76/1.04  prop_fo_subsumed:                       9
% 2.76/1.04  prop_solver_time:                       0.
% 2.76/1.04  smt_solver_time:                        0.
% 2.76/1.04  smt_fast_solver_time:                   0.
% 2.76/1.04  prop_fast_solver_time:                  0.
% 2.76/1.04  prop_unsat_core_time:                   0.
% 2.76/1.04  
% 2.76/1.04  ------ QBF
% 2.76/1.04  
% 2.76/1.04  qbf_q_res:                              0
% 2.76/1.04  qbf_num_tautologies:                    0
% 2.76/1.04  qbf_prep_cycles:                        0
% 2.76/1.04  
% 2.76/1.04  ------ BMC1
% 2.76/1.04  
% 2.76/1.04  bmc1_current_bound:                     -1
% 2.76/1.04  bmc1_last_solved_bound:                 -1
% 2.76/1.04  bmc1_unsat_core_size:                   -1
% 2.76/1.04  bmc1_unsat_core_parents_size:           -1
% 2.76/1.04  bmc1_merge_next_fun:                    0
% 2.76/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.76/1.04  
% 2.76/1.04  ------ Instantiation
% 2.76/1.04  
% 2.76/1.04  inst_num_of_clauses:                    402
% 2.76/1.04  inst_num_in_passive:                    138
% 2.76/1.04  inst_num_in_active:                     189
% 2.76/1.04  inst_num_in_unprocessed:                75
% 2.76/1.04  inst_num_of_loops:                      210
% 2.76/1.04  inst_num_of_learning_restarts:          0
% 2.76/1.04  inst_num_moves_active_passive:          19
% 2.76/1.04  inst_lit_activity:                      0
% 2.76/1.04  inst_lit_activity_moves:                0
% 2.76/1.04  inst_num_tautologies:                   0
% 2.76/1.04  inst_num_prop_implied:                  0
% 2.76/1.04  inst_num_existing_simplified:           0
% 2.76/1.04  inst_num_eq_res_simplified:             0
% 2.76/1.04  inst_num_child_elim:                    0
% 2.76/1.04  inst_num_of_dismatching_blockings:      234
% 2.76/1.04  inst_num_of_non_proper_insts:           459
% 2.76/1.04  inst_num_of_duplicates:                 0
% 2.76/1.04  inst_inst_num_from_inst_to_res:         0
% 2.76/1.04  inst_dismatching_checking_time:         0.
% 2.76/1.04  
% 2.76/1.04  ------ Resolution
% 2.76/1.04  
% 2.76/1.04  res_num_of_clauses:                     0
% 2.76/1.04  res_num_in_passive:                     0
% 2.76/1.04  res_num_in_active:                      0
% 2.76/1.04  res_num_of_loops:                       124
% 2.76/1.04  res_forward_subset_subsumed:            96
% 2.76/1.04  res_backward_subset_subsumed:           0
% 2.76/1.04  res_forward_subsumed:                   0
% 2.76/1.04  res_backward_subsumed:                  0
% 2.76/1.04  res_forward_subsumption_resolution:     0
% 2.76/1.04  res_backward_subsumption_resolution:    0
% 2.76/1.04  res_clause_to_clause_subsumption:       82
% 2.76/1.04  res_orphan_elimination:                 0
% 2.76/1.04  res_tautology_del:                      36
% 2.76/1.04  res_num_eq_res_simplified:              1
% 2.76/1.04  res_num_sel_changes:                    0
% 2.76/1.04  res_moves_from_active_to_pass:          0
% 2.76/1.04  
% 2.76/1.04  ------ Superposition
% 2.76/1.04  
% 2.76/1.04  sup_time_total:                         0.
% 2.76/1.04  sup_time_generating:                    0.
% 2.76/1.04  sup_time_sim_full:                      0.
% 2.76/1.04  sup_time_sim_immed:                     0.
% 2.76/1.04  
% 2.76/1.04  sup_num_of_clauses:                     46
% 2.76/1.04  sup_num_in_active:                      32
% 2.76/1.04  sup_num_in_passive:                     14
% 2.76/1.04  sup_num_of_loops:                       41
% 2.76/1.04  sup_fw_superposition:                   12
% 2.76/1.04  sup_bw_superposition:                   17
% 2.76/1.04  sup_immediate_simplified:               0
% 2.76/1.04  sup_given_eliminated:                   0
% 2.76/1.04  comparisons_done:                       0
% 2.76/1.04  comparisons_avoided:                    13
% 2.76/1.04  
% 2.76/1.04  ------ Simplifications
% 2.76/1.04  
% 2.76/1.04  
% 2.76/1.04  sim_fw_subset_subsumed:                 0
% 2.76/1.04  sim_bw_subset_subsumed:                 0
% 2.76/1.04  sim_fw_subsumed:                        0
% 2.76/1.04  sim_bw_subsumed:                        0
% 2.76/1.04  sim_fw_subsumption_res:                 0
% 2.76/1.04  sim_bw_subsumption_res:                 0
% 2.76/1.04  sim_tautology_del:                      0
% 2.76/1.04  sim_eq_tautology_del:                   2
% 2.76/1.04  sim_eq_res_simp:                        0
% 2.76/1.04  sim_fw_demodulated:                     0
% 2.76/1.04  sim_bw_demodulated:                     10
% 2.76/1.04  sim_light_normalised:                   3
% 2.76/1.04  sim_joinable_taut:                      0
% 2.76/1.04  sim_joinable_simp:                      0
% 2.76/1.04  sim_ac_normalised:                      0
% 2.76/1.04  sim_smt_subsumption:                    0
% 2.76/1.04  
%------------------------------------------------------------------------------
