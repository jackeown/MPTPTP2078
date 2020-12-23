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
% DateTime   : Thu Dec  3 12:05:46 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 835 expanded)
%              Number of clauses        :   75 ( 229 expanded)
%              Number of leaves         :   15 ( 190 expanded)
%              Depth                    :   20
%              Number of atoms          :  381 (2475 expanded)
%              Number of equality atoms :  222 ( 979 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,
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

fof(f33,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f32])).

fof(f56,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f71,plain,(
    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f22])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f58,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f74,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f75,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f59,f60,f60])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_356,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_357,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_763,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_enumset1(sK1,sK1,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | sK2 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_357])).

cnf(c_764,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_765,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_20])).

cnf(c_766,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_765])).

cnf(c_824,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_766])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_401,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_402,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_1482,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_402])).

cnf(c_1550,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_824,c_1482])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1352,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1627,plain,
    ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1352])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_410,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_411,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_281,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_522,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_411,c_281])).

cnf(c_1062,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_522])).

cnf(c_1348,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_1063,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_522])).

cnf(c_1105,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_1106,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1062])).

cnf(c_1065,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1483,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_557,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_411])).

cnf(c_558,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_1057,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_558])).

cnf(c_1484,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_1489,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1484])).

cnf(c_2932,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_1105,c_1106,c_1483,c_1489])).

cnf(c_2933,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2932])).

cnf(c_2941,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1627,c_2933])).

cnf(c_1058,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_558])).

cnf(c_1342,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_1059,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_558])).

cnf(c_2291,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1342,c_1059,c_1058,c_1483,c_1484])).

cnf(c_2295,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1550,c_2291])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_536,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_411])).

cnf(c_537,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_1485,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1622,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_1483,c_1485])).

cnf(c_2300,plain,
    ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2295,c_1622])).

cnf(c_2943,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2941,c_2300])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1350,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1555,plain,
    ( r1_tarski(k7_relset_1(k1_relat_1(sK4),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1550,c_1350])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_392,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_393,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_1495,plain,
    ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_393])).

cnf(c_1759,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_1495,c_1550])).

cnf(c_1855,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1555,c_1759])).

cnf(c_3333,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2943,c_1855])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_545,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_411])).

cnf(c_546,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4))
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_1060,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4))
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_546])).

cnf(c_1345,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1060])).

cnf(c_1061,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_546])).

cnf(c_1100,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1061])).

cnf(c_1101,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1060])).

cnf(c_2172,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_1100,c_1101,c_1483,c_1489])).

cnf(c_4864,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3333,c_2172])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.85/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/0.99  
% 2.85/0.99  ------  iProver source info
% 2.85/0.99  
% 2.85/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.85/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/0.99  git: non_committed_changes: false
% 2.85/0.99  git: last_make_outside_of_git: false
% 2.85/0.99  
% 2.85/0.99  ------ 
% 2.85/0.99  
% 2.85/0.99  ------ Input Options
% 2.85/0.99  
% 2.85/0.99  --out_options                           all
% 2.85/0.99  --tptp_safe_out                         true
% 2.85/0.99  --problem_path                          ""
% 2.85/0.99  --include_path                          ""
% 2.85/0.99  --clausifier                            res/vclausify_rel
% 2.85/0.99  --clausifier_options                    --mode clausify
% 2.85/0.99  --stdin                                 false
% 2.85/0.99  --stats_out                             all
% 2.85/0.99  
% 2.85/0.99  ------ General Options
% 2.85/0.99  
% 2.85/0.99  --fof                                   false
% 2.85/0.99  --time_out_real                         305.
% 2.85/0.99  --time_out_virtual                      -1.
% 2.85/0.99  --symbol_type_check                     false
% 2.85/0.99  --clausify_out                          false
% 2.85/0.99  --sig_cnt_out                           false
% 2.85/0.99  --trig_cnt_out                          false
% 2.85/0.99  --trig_cnt_out_tolerance                1.
% 2.85/0.99  --trig_cnt_out_sk_spl                   false
% 2.85/0.99  --abstr_cl_out                          false
% 2.85/0.99  
% 2.85/0.99  ------ Global Options
% 2.85/0.99  
% 2.85/0.99  --schedule                              default
% 2.85/0.99  --add_important_lit                     false
% 2.85/0.99  --prop_solver_per_cl                    1000
% 2.85/0.99  --min_unsat_core                        false
% 2.85/0.99  --soft_assumptions                      false
% 2.85/0.99  --soft_lemma_size                       3
% 2.85/0.99  --prop_impl_unit_size                   0
% 2.85/0.99  --prop_impl_unit                        []
% 2.85/0.99  --share_sel_clauses                     true
% 2.85/0.99  --reset_solvers                         false
% 2.85/0.99  --bc_imp_inh                            [conj_cone]
% 2.85/0.99  --conj_cone_tolerance                   3.
% 2.85/0.99  --extra_neg_conj                        none
% 2.85/0.99  --large_theory_mode                     true
% 2.85/0.99  --prolific_symb_bound                   200
% 2.85/0.99  --lt_threshold                          2000
% 2.85/0.99  --clause_weak_htbl                      true
% 2.85/0.99  --gc_record_bc_elim                     false
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing Options
% 2.85/0.99  
% 2.85/0.99  --preprocessing_flag                    true
% 2.85/0.99  --time_out_prep_mult                    0.1
% 2.85/0.99  --splitting_mode                        input
% 2.85/0.99  --splitting_grd                         true
% 2.85/0.99  --splitting_cvd                         false
% 2.85/0.99  --splitting_cvd_svl                     false
% 2.85/0.99  --splitting_nvd                         32
% 2.85/0.99  --sub_typing                            true
% 2.85/0.99  --prep_gs_sim                           true
% 2.85/0.99  --prep_unflatten                        true
% 2.85/0.99  --prep_res_sim                          true
% 2.85/0.99  --prep_upred                            true
% 2.85/0.99  --prep_sem_filter                       exhaustive
% 2.85/0.99  --prep_sem_filter_out                   false
% 2.85/0.99  --pred_elim                             true
% 2.85/0.99  --res_sim_input                         true
% 2.85/0.99  --eq_ax_congr_red                       true
% 2.85/0.99  --pure_diseq_elim                       true
% 2.85/0.99  --brand_transform                       false
% 2.85/0.99  --non_eq_to_eq                          false
% 2.85/0.99  --prep_def_merge                        true
% 2.85/0.99  --prep_def_merge_prop_impl              false
% 2.85/0.99  --prep_def_merge_mbd                    true
% 2.85/0.99  --prep_def_merge_tr_red                 false
% 2.85/0.99  --prep_def_merge_tr_cl                  false
% 2.85/0.99  --smt_preprocessing                     true
% 2.85/0.99  --smt_ac_axioms                         fast
% 2.85/0.99  --preprocessed_out                      false
% 2.85/0.99  --preprocessed_stats                    false
% 2.85/0.99  
% 2.85/0.99  ------ Abstraction refinement Options
% 2.85/0.99  
% 2.85/0.99  --abstr_ref                             []
% 2.85/0.99  --abstr_ref_prep                        false
% 2.85/0.99  --abstr_ref_until_sat                   false
% 2.85/0.99  --abstr_ref_sig_restrict                funpre
% 2.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.99  --abstr_ref_under                       []
% 2.85/0.99  
% 2.85/0.99  ------ SAT Options
% 2.85/0.99  
% 2.85/0.99  --sat_mode                              false
% 2.85/0.99  --sat_fm_restart_options                ""
% 2.85/0.99  --sat_gr_def                            false
% 2.85/0.99  --sat_epr_types                         true
% 2.85/0.99  --sat_non_cyclic_types                  false
% 2.85/0.99  --sat_finite_models                     false
% 2.85/0.99  --sat_fm_lemmas                         false
% 2.85/0.99  --sat_fm_prep                           false
% 2.85/0.99  --sat_fm_uc_incr                        true
% 2.85/0.99  --sat_out_model                         small
% 2.85/0.99  --sat_out_clauses                       false
% 2.85/0.99  
% 2.85/0.99  ------ QBF Options
% 2.85/0.99  
% 2.85/0.99  --qbf_mode                              false
% 2.85/0.99  --qbf_elim_univ                         false
% 2.85/0.99  --qbf_dom_inst                          none
% 2.85/0.99  --qbf_dom_pre_inst                      false
% 2.85/0.99  --qbf_sk_in                             false
% 2.85/0.99  --qbf_pred_elim                         true
% 2.85/0.99  --qbf_split                             512
% 2.85/0.99  
% 2.85/0.99  ------ BMC1 Options
% 2.85/0.99  
% 2.85/0.99  --bmc1_incremental                      false
% 2.85/0.99  --bmc1_axioms                           reachable_all
% 2.85/0.99  --bmc1_min_bound                        0
% 2.85/0.99  --bmc1_max_bound                        -1
% 2.85/0.99  --bmc1_max_bound_default                -1
% 2.85/0.99  --bmc1_symbol_reachability              true
% 2.85/0.99  --bmc1_property_lemmas                  false
% 2.85/0.99  --bmc1_k_induction                      false
% 2.85/0.99  --bmc1_non_equiv_states                 false
% 2.85/0.99  --bmc1_deadlock                         false
% 2.85/0.99  --bmc1_ucm                              false
% 2.85/0.99  --bmc1_add_unsat_core                   none
% 2.85/0.99  --bmc1_unsat_core_children              false
% 2.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.99  --bmc1_out_stat                         full
% 2.85/0.99  --bmc1_ground_init                      false
% 2.85/0.99  --bmc1_pre_inst_next_state              false
% 2.85/0.99  --bmc1_pre_inst_state                   false
% 2.85/0.99  --bmc1_pre_inst_reach_state             false
% 2.85/0.99  --bmc1_out_unsat_core                   false
% 2.85/0.99  --bmc1_aig_witness_out                  false
% 2.85/0.99  --bmc1_verbose                          false
% 2.85/0.99  --bmc1_dump_clauses_tptp                false
% 2.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.99  --bmc1_dump_file                        -
% 2.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.99  --bmc1_ucm_extend_mode                  1
% 2.85/0.99  --bmc1_ucm_init_mode                    2
% 2.85/0.99  --bmc1_ucm_cone_mode                    none
% 2.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.99  --bmc1_ucm_relax_model                  4
% 2.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.99  --bmc1_ucm_layered_model                none
% 2.85/0.99  --bmc1_ucm_max_lemma_size               10
% 2.85/0.99  
% 2.85/0.99  ------ AIG Options
% 2.85/0.99  
% 2.85/0.99  --aig_mode                              false
% 2.85/0.99  
% 2.85/0.99  ------ Instantiation Options
% 2.85/0.99  
% 2.85/0.99  --instantiation_flag                    true
% 2.85/0.99  --inst_sos_flag                         false
% 2.85/0.99  --inst_sos_phase                        true
% 2.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel_side                     num_symb
% 2.85/0.99  --inst_solver_per_active                1400
% 2.85/0.99  --inst_solver_calls_frac                1.
% 2.85/0.99  --inst_passive_queue_type               priority_queues
% 2.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.99  --inst_passive_queues_freq              [25;2]
% 2.85/0.99  --inst_dismatching                      true
% 2.85/0.99  --inst_eager_unprocessed_to_passive     true
% 2.85/0.99  --inst_prop_sim_given                   true
% 2.85/0.99  --inst_prop_sim_new                     false
% 2.85/0.99  --inst_subs_new                         false
% 2.85/0.99  --inst_eq_res_simp                      false
% 2.85/0.99  --inst_subs_given                       false
% 2.85/0.99  --inst_orphan_elimination               true
% 2.85/0.99  --inst_learning_loop_flag               true
% 2.85/0.99  --inst_learning_start                   3000
% 2.85/0.99  --inst_learning_factor                  2
% 2.85/0.99  --inst_start_prop_sim_after_learn       3
% 2.85/0.99  --inst_sel_renew                        solver
% 2.85/0.99  --inst_lit_activity_flag                true
% 2.85/0.99  --inst_restr_to_given                   false
% 2.85/0.99  --inst_activity_threshold               500
% 2.85/0.99  --inst_out_proof                        true
% 2.85/0.99  
% 2.85/0.99  ------ Resolution Options
% 2.85/0.99  
% 2.85/0.99  --resolution_flag                       true
% 2.85/0.99  --res_lit_sel                           adaptive
% 2.85/0.99  --res_lit_sel_side                      none
% 2.85/0.99  --res_ordering                          kbo
% 2.85/0.99  --res_to_prop_solver                    active
% 2.85/0.99  --res_prop_simpl_new                    false
% 2.85/0.99  --res_prop_simpl_given                  true
% 2.85/0.99  --res_passive_queue_type                priority_queues
% 2.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.99  --res_passive_queues_freq               [15;5]
% 2.85/0.99  --res_forward_subs                      full
% 2.85/0.99  --res_backward_subs                     full
% 2.85/0.99  --res_forward_subs_resolution           true
% 2.85/0.99  --res_backward_subs_resolution          true
% 2.85/0.99  --res_orphan_elimination                true
% 2.85/0.99  --res_time_limit                        2.
% 2.85/0.99  --res_out_proof                         true
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Options
% 2.85/0.99  
% 2.85/0.99  --superposition_flag                    true
% 2.85/0.99  --sup_passive_queue_type                priority_queues
% 2.85/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.99  --demod_completeness_check              fast
% 2.85/0.99  --demod_use_ground                      true
% 2.85/0.99  --sup_to_prop_solver                    passive
% 2.85/0.99  --sup_prop_simpl_new                    true
% 2.85/0.99  --sup_prop_simpl_given                  true
% 2.85/0.99  --sup_fun_splitting                     false
% 2.85/0.99  --sup_smt_interval                      50000
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Simplification Setup
% 2.85/0.99  
% 2.85/0.99  --sup_indices_passive                   []
% 2.85/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_full_bw                           [BwDemod]
% 2.85/0.99  --sup_immed_triv                        [TrivRules]
% 2.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_immed_bw_main                     []
% 2.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  
% 2.85/0.99  ------ Combination Options
% 2.85/0.99  
% 2.85/0.99  --comb_res_mult                         3
% 2.85/0.99  --comb_sup_mult                         2
% 2.85/0.99  --comb_inst_mult                        10
% 2.85/0.99  
% 2.85/0.99  ------ Debug Options
% 2.85/0.99  
% 2.85/0.99  --dbg_backtrace                         false
% 2.85/0.99  --dbg_dump_prop_clauses                 false
% 2.85/0.99  --dbg_dump_prop_clauses_file            -
% 2.85/0.99  --dbg_out_stat                          false
% 2.85/0.99  ------ Parsing...
% 2.85/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/0.99  ------ Proving...
% 2.85/0.99  ------ Problem Properties 
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  clauses                                 23
% 2.85/0.99  conjectures                             2
% 2.85/0.99  EPR                                     4
% 2.85/0.99  Horn                                    17
% 2.85/0.99  unary                                   5
% 2.85/0.99  binary                                  11
% 2.85/0.99  lits                                    50
% 2.85/0.99  lits eq                                 29
% 2.85/0.99  fd_pure                                 0
% 2.85/0.99  fd_pseudo                               0
% 2.85/0.99  fd_cond                                 0
% 2.85/0.99  fd_pseudo_cond                          3
% 2.85/0.99  AC symbols                              0
% 2.85/0.99  
% 2.85/0.99  ------ Schedule dynamic 5 is on 
% 2.85/0.99  
% 2.85/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  ------ 
% 2.85/0.99  Current options:
% 2.85/0.99  ------ 
% 2.85/0.99  
% 2.85/0.99  ------ Input Options
% 2.85/0.99  
% 2.85/0.99  --out_options                           all
% 2.85/0.99  --tptp_safe_out                         true
% 2.85/0.99  --problem_path                          ""
% 2.85/0.99  --include_path                          ""
% 2.85/0.99  --clausifier                            res/vclausify_rel
% 2.85/0.99  --clausifier_options                    --mode clausify
% 2.85/0.99  --stdin                                 false
% 2.85/0.99  --stats_out                             all
% 2.85/0.99  
% 2.85/0.99  ------ General Options
% 2.85/0.99  
% 2.85/0.99  --fof                                   false
% 2.85/0.99  --time_out_real                         305.
% 2.85/0.99  --time_out_virtual                      -1.
% 2.85/0.99  --symbol_type_check                     false
% 2.85/0.99  --clausify_out                          false
% 2.85/0.99  --sig_cnt_out                           false
% 2.85/0.99  --trig_cnt_out                          false
% 2.85/0.99  --trig_cnt_out_tolerance                1.
% 2.85/0.99  --trig_cnt_out_sk_spl                   false
% 2.85/0.99  --abstr_cl_out                          false
% 2.85/0.99  
% 2.85/0.99  ------ Global Options
% 2.85/0.99  
% 2.85/0.99  --schedule                              default
% 2.85/0.99  --add_important_lit                     false
% 2.85/0.99  --prop_solver_per_cl                    1000
% 2.85/0.99  --min_unsat_core                        false
% 2.85/0.99  --soft_assumptions                      false
% 2.85/0.99  --soft_lemma_size                       3
% 2.85/0.99  --prop_impl_unit_size                   0
% 2.85/0.99  --prop_impl_unit                        []
% 2.85/0.99  --share_sel_clauses                     true
% 2.85/0.99  --reset_solvers                         false
% 2.85/0.99  --bc_imp_inh                            [conj_cone]
% 2.85/0.99  --conj_cone_tolerance                   3.
% 2.85/0.99  --extra_neg_conj                        none
% 2.85/0.99  --large_theory_mode                     true
% 2.85/0.99  --prolific_symb_bound                   200
% 2.85/0.99  --lt_threshold                          2000
% 2.85/0.99  --clause_weak_htbl                      true
% 2.85/0.99  --gc_record_bc_elim                     false
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing Options
% 2.85/0.99  
% 2.85/0.99  --preprocessing_flag                    true
% 2.85/0.99  --time_out_prep_mult                    0.1
% 2.85/0.99  --splitting_mode                        input
% 2.85/0.99  --splitting_grd                         true
% 2.85/0.99  --splitting_cvd                         false
% 2.85/0.99  --splitting_cvd_svl                     false
% 2.85/0.99  --splitting_nvd                         32
% 2.85/0.99  --sub_typing                            true
% 2.85/0.99  --prep_gs_sim                           true
% 2.85/0.99  --prep_unflatten                        true
% 2.85/0.99  --prep_res_sim                          true
% 2.85/0.99  --prep_upred                            true
% 2.85/0.99  --prep_sem_filter                       exhaustive
% 2.85/0.99  --prep_sem_filter_out                   false
% 2.85/0.99  --pred_elim                             true
% 2.85/0.99  --res_sim_input                         true
% 2.85/0.99  --eq_ax_congr_red                       true
% 2.85/0.99  --pure_diseq_elim                       true
% 2.85/0.99  --brand_transform                       false
% 2.85/0.99  --non_eq_to_eq                          false
% 2.85/0.99  --prep_def_merge                        true
% 2.85/0.99  --prep_def_merge_prop_impl              false
% 2.85/0.99  --prep_def_merge_mbd                    true
% 2.85/0.99  --prep_def_merge_tr_red                 false
% 2.85/0.99  --prep_def_merge_tr_cl                  false
% 2.85/0.99  --smt_preprocessing                     true
% 2.85/0.99  --smt_ac_axioms                         fast
% 2.85/0.99  --preprocessed_out                      false
% 2.85/0.99  --preprocessed_stats                    false
% 2.85/0.99  
% 2.85/0.99  ------ Abstraction refinement Options
% 2.85/0.99  
% 2.85/0.99  --abstr_ref                             []
% 2.85/0.99  --abstr_ref_prep                        false
% 2.85/0.99  --abstr_ref_until_sat                   false
% 2.85/0.99  --abstr_ref_sig_restrict                funpre
% 2.85/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/0.99  --abstr_ref_under                       []
% 2.85/0.99  
% 2.85/0.99  ------ SAT Options
% 2.85/0.99  
% 2.85/0.99  --sat_mode                              false
% 2.85/0.99  --sat_fm_restart_options                ""
% 2.85/0.99  --sat_gr_def                            false
% 2.85/0.99  --sat_epr_types                         true
% 2.85/0.99  --sat_non_cyclic_types                  false
% 2.85/0.99  --sat_finite_models                     false
% 2.85/0.99  --sat_fm_lemmas                         false
% 2.85/0.99  --sat_fm_prep                           false
% 2.85/0.99  --sat_fm_uc_incr                        true
% 2.85/0.99  --sat_out_model                         small
% 2.85/0.99  --sat_out_clauses                       false
% 2.85/0.99  
% 2.85/0.99  ------ QBF Options
% 2.85/0.99  
% 2.85/0.99  --qbf_mode                              false
% 2.85/0.99  --qbf_elim_univ                         false
% 2.85/0.99  --qbf_dom_inst                          none
% 2.85/0.99  --qbf_dom_pre_inst                      false
% 2.85/0.99  --qbf_sk_in                             false
% 2.85/0.99  --qbf_pred_elim                         true
% 2.85/0.99  --qbf_split                             512
% 2.85/0.99  
% 2.85/0.99  ------ BMC1 Options
% 2.85/0.99  
% 2.85/0.99  --bmc1_incremental                      false
% 2.85/0.99  --bmc1_axioms                           reachable_all
% 2.85/0.99  --bmc1_min_bound                        0
% 2.85/0.99  --bmc1_max_bound                        -1
% 2.85/0.99  --bmc1_max_bound_default                -1
% 2.85/0.99  --bmc1_symbol_reachability              true
% 2.85/0.99  --bmc1_property_lemmas                  false
% 2.85/0.99  --bmc1_k_induction                      false
% 2.85/0.99  --bmc1_non_equiv_states                 false
% 2.85/0.99  --bmc1_deadlock                         false
% 2.85/0.99  --bmc1_ucm                              false
% 2.85/0.99  --bmc1_add_unsat_core                   none
% 2.85/0.99  --bmc1_unsat_core_children              false
% 2.85/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/0.99  --bmc1_out_stat                         full
% 2.85/0.99  --bmc1_ground_init                      false
% 2.85/0.99  --bmc1_pre_inst_next_state              false
% 2.85/0.99  --bmc1_pre_inst_state                   false
% 2.85/0.99  --bmc1_pre_inst_reach_state             false
% 2.85/0.99  --bmc1_out_unsat_core                   false
% 2.85/0.99  --bmc1_aig_witness_out                  false
% 2.85/0.99  --bmc1_verbose                          false
% 2.85/0.99  --bmc1_dump_clauses_tptp                false
% 2.85/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.85/0.99  --bmc1_dump_file                        -
% 2.85/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.85/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.85/0.99  --bmc1_ucm_extend_mode                  1
% 2.85/0.99  --bmc1_ucm_init_mode                    2
% 2.85/0.99  --bmc1_ucm_cone_mode                    none
% 2.85/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.85/0.99  --bmc1_ucm_relax_model                  4
% 2.85/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.85/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/0.99  --bmc1_ucm_layered_model                none
% 2.85/0.99  --bmc1_ucm_max_lemma_size               10
% 2.85/0.99  
% 2.85/0.99  ------ AIG Options
% 2.85/0.99  
% 2.85/0.99  --aig_mode                              false
% 2.85/0.99  
% 2.85/0.99  ------ Instantiation Options
% 2.85/0.99  
% 2.85/0.99  --instantiation_flag                    true
% 2.85/0.99  --inst_sos_flag                         false
% 2.85/0.99  --inst_sos_phase                        true
% 2.85/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/0.99  --inst_lit_sel_side                     none
% 2.85/0.99  --inst_solver_per_active                1400
% 2.85/0.99  --inst_solver_calls_frac                1.
% 2.85/0.99  --inst_passive_queue_type               priority_queues
% 2.85/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/0.99  --inst_passive_queues_freq              [25;2]
% 2.85/0.99  --inst_dismatching                      true
% 2.85/0.99  --inst_eager_unprocessed_to_passive     true
% 2.85/0.99  --inst_prop_sim_given                   true
% 2.85/0.99  --inst_prop_sim_new                     false
% 2.85/0.99  --inst_subs_new                         false
% 2.85/0.99  --inst_eq_res_simp                      false
% 2.85/0.99  --inst_subs_given                       false
% 2.85/0.99  --inst_orphan_elimination               true
% 2.85/0.99  --inst_learning_loop_flag               true
% 2.85/0.99  --inst_learning_start                   3000
% 2.85/0.99  --inst_learning_factor                  2
% 2.85/0.99  --inst_start_prop_sim_after_learn       3
% 2.85/0.99  --inst_sel_renew                        solver
% 2.85/0.99  --inst_lit_activity_flag                true
% 2.85/0.99  --inst_restr_to_given                   false
% 2.85/0.99  --inst_activity_threshold               500
% 2.85/0.99  --inst_out_proof                        true
% 2.85/0.99  
% 2.85/0.99  ------ Resolution Options
% 2.85/0.99  
% 2.85/0.99  --resolution_flag                       false
% 2.85/0.99  --res_lit_sel                           adaptive
% 2.85/0.99  --res_lit_sel_side                      none
% 2.85/0.99  --res_ordering                          kbo
% 2.85/0.99  --res_to_prop_solver                    active
% 2.85/0.99  --res_prop_simpl_new                    false
% 2.85/0.99  --res_prop_simpl_given                  true
% 2.85/0.99  --res_passive_queue_type                priority_queues
% 2.85/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/0.99  --res_passive_queues_freq               [15;5]
% 2.85/0.99  --res_forward_subs                      full
% 2.85/0.99  --res_backward_subs                     full
% 2.85/0.99  --res_forward_subs_resolution           true
% 2.85/0.99  --res_backward_subs_resolution          true
% 2.85/0.99  --res_orphan_elimination                true
% 2.85/0.99  --res_time_limit                        2.
% 2.85/0.99  --res_out_proof                         true
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Options
% 2.85/0.99  
% 2.85/0.99  --superposition_flag                    true
% 2.85/0.99  --sup_passive_queue_type                priority_queues
% 2.85/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.85/0.99  --demod_completeness_check              fast
% 2.85/0.99  --demod_use_ground                      true
% 2.85/0.99  --sup_to_prop_solver                    passive
% 2.85/0.99  --sup_prop_simpl_new                    true
% 2.85/0.99  --sup_prop_simpl_given                  true
% 2.85/0.99  --sup_fun_splitting                     false
% 2.85/0.99  --sup_smt_interval                      50000
% 2.85/0.99  
% 2.85/0.99  ------ Superposition Simplification Setup
% 2.85/0.99  
% 2.85/0.99  --sup_indices_passive                   []
% 2.85/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_full_bw                           [BwDemod]
% 2.85/0.99  --sup_immed_triv                        [TrivRules]
% 2.85/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_immed_bw_main                     []
% 2.85/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/0.99  
% 2.85/0.99  ------ Combination Options
% 2.85/0.99  
% 2.85/0.99  --comb_res_mult                         3
% 2.85/0.99  --comb_sup_mult                         2
% 2.85/0.99  --comb_inst_mult                        10
% 2.85/0.99  
% 2.85/0.99  ------ Debug Options
% 2.85/0.99  
% 2.85/0.99  --dbg_backtrace                         false
% 2.85/0.99  --dbg_dump_prop_clauses                 false
% 2.85/0.99  --dbg_dump_prop_clauses_file            -
% 2.85/0.99  --dbg_out_stat                          false
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  ------ Proving...
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  % SZS status Theorem for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99   Resolution empty clause
% 2.85/0.99  
% 2.85/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  fof(f12,conjecture,(
% 2.85/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f13,negated_conjecture,(
% 2.85/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.85/0.99    inference(negated_conjecture,[],[f12])).
% 2.85/0.99  
% 2.85/0.99  fof(f24,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.85/0.99    inference(ennf_transformation,[],[f13])).
% 2.85/0.99  
% 2.85/0.99  fof(f25,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.85/0.99    inference(flattening,[],[f24])).
% 2.85/0.99  
% 2.85/0.99  fof(f32,plain,(
% 2.85/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f33,plain,(
% 2.85/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f32])).
% 2.85/0.99  
% 2.85/0.99  fof(f56,plain,(
% 2.85/0.99    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 2.85/0.99    inference(cnf_transformation,[],[f33])).
% 2.85/0.99  
% 2.85/0.99  fof(f2,axiom,(
% 2.85/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f40,plain,(
% 2.85/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f2])).
% 2.85/0.99  
% 2.85/0.99  fof(f3,axiom,(
% 2.85/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f41,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f3])).
% 2.85/0.99  
% 2.85/0.99  fof(f60,plain,(
% 2.85/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.85/0.99    inference(definition_unfolding,[],[f40,f41])).
% 2.85/0.99  
% 2.85/0.99  fof(f71,plain,(
% 2.85/0.99    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2)),
% 2.85/0.99    inference(definition_unfolding,[],[f56,f60])).
% 2.85/0.99  
% 2.85/0.99  fof(f11,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f22,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f11])).
% 2.85/0.99  
% 2.85/0.99  fof(f23,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(flattening,[],[f22])).
% 2.85/0.99  
% 2.85/0.99  fof(f31,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(nnf_transformation,[],[f23])).
% 2.85/0.99  
% 2.85/0.99  fof(f49,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f31])).
% 2.85/0.99  
% 2.85/0.99  fof(f57,plain,(
% 2.85/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.85/0.99    inference(cnf_transformation,[],[f33])).
% 2.85/0.99  
% 2.85/0.99  fof(f70,plain,(
% 2.85/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 2.85/0.99    inference(definition_unfolding,[],[f57,f60])).
% 2.85/0.99  
% 2.85/0.99  fof(f58,plain,(
% 2.85/0.99    k1_xboole_0 != sK2),
% 2.85/0.99    inference(cnf_transformation,[],[f33])).
% 2.85/0.99  
% 2.85/0.99  fof(f9,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f20,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f9])).
% 2.85/0.99  
% 2.85/0.99  fof(f47,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f20])).
% 2.85/0.99  
% 2.85/0.99  fof(f1,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f26,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.85/0.99    inference(nnf_transformation,[],[f1])).
% 2.85/0.99  
% 2.85/0.99  fof(f27,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.85/0.99    inference(flattening,[],[f26])).
% 2.85/0.99  
% 2.85/0.99  fof(f28,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.85/0.99    inference(rectify,[],[f27])).
% 2.85/0.99  
% 2.85/0.99  fof(f29,plain,(
% 2.85/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.85/0.99    introduced(choice_axiom,[])).
% 2.85/0.99  
% 2.85/0.99  fof(f30,plain,(
% 2.85/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.85/0.99  
% 2.85/0.99  fof(f35,plain,(
% 2.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.85/0.99    inference(cnf_transformation,[],[f30])).
% 2.85/0.99  
% 2.85/0.99  fof(f65,plain,(
% 2.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 2.85/0.99    inference(definition_unfolding,[],[f35,f41])).
% 2.85/0.99  
% 2.85/0.99  fof(f74,plain,(
% 2.85/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 2.85/0.99    inference(equality_resolution,[],[f65])).
% 2.85/0.99  
% 2.85/0.99  fof(f75,plain,(
% 2.85/0.99    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 2.85/0.99    inference(equality_resolution,[],[f74])).
% 2.85/0.99  
% 2.85/0.99  fof(f8,axiom,(
% 2.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f19,plain,(
% 2.85/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f8])).
% 2.85/0.99  
% 2.85/0.99  fof(f46,plain,(
% 2.85/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f19])).
% 2.85/0.99  
% 2.85/0.99  fof(f7,axiom,(
% 2.85/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f17,plain,(
% 2.85/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.85/0.99    inference(ennf_transformation,[],[f7])).
% 2.85/0.99  
% 2.85/0.99  fof(f18,plain,(
% 2.85/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.85/0.99    inference(flattening,[],[f17])).
% 2.85/0.99  
% 2.85/0.99  fof(f45,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f18])).
% 2.85/0.99  
% 2.85/0.99  fof(f68,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.85/0.99    inference(definition_unfolding,[],[f45,f60])).
% 2.85/0.99  
% 2.85/0.99  fof(f55,plain,(
% 2.85/0.99    v1_funct_1(sK4)),
% 2.85/0.99    inference(cnf_transformation,[],[f33])).
% 2.85/0.99  
% 2.85/0.99  fof(f4,axiom,(
% 2.85/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f14,plain,(
% 2.85/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.85/0.99    inference(ennf_transformation,[],[f4])).
% 2.85/0.99  
% 2.85/0.99  fof(f42,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f14])).
% 2.85/0.99  
% 2.85/0.99  fof(f67,plain,(
% 2.85/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(definition_unfolding,[],[f42,f60])).
% 2.85/0.99  
% 2.85/0.99  fof(f6,axiom,(
% 2.85/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f16,plain,(
% 2.85/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.85/0.99    inference(ennf_transformation,[],[f6])).
% 2.85/0.99  
% 2.85/0.99  fof(f44,plain,(
% 2.85/0.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f16])).
% 2.85/0.99  
% 2.85/0.99  fof(f59,plain,(
% 2.85/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 2.85/0.99    inference(cnf_transformation,[],[f33])).
% 2.85/0.99  
% 2.85/0.99  fof(f69,plain,(
% 2.85/0.99    ~r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 2.85/0.99    inference(definition_unfolding,[],[f59,f60,f60])).
% 2.85/0.99  
% 2.85/0.99  fof(f10,axiom,(
% 2.85/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f21,plain,(
% 2.85/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.85/0.99    inference(ennf_transformation,[],[f10])).
% 2.85/0.99  
% 2.85/0.99  fof(f48,plain,(
% 2.85/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.85/0.99    inference(cnf_transformation,[],[f21])).
% 2.85/0.99  
% 2.85/0.99  fof(f5,axiom,(
% 2.85/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/0.99  
% 2.85/0.99  fof(f15,plain,(
% 2.85/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.85/0.99    inference(ennf_transformation,[],[f5])).
% 2.85/0.99  
% 2.85/0.99  fof(f43,plain,(
% 2.85/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.85/0.99    inference(cnf_transformation,[],[f15])).
% 2.85/0.99  
% 2.85/0.99  cnf(c_22,negated_conjecture,
% 2.85/0.99      ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 2.85/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_18,plain,
% 2.85/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.99      | k1_xboole_0 = X2 ),
% 2.85/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_21,negated_conjecture,
% 2.85/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 2.85/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_356,plain,
% 2.85/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.85/0.99      | sK4 != X0
% 2.85/0.99      | k1_xboole_0 = X2 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_357,plain,
% 2.85/0.99      ( ~ v1_funct_2(sK4,X0,X1)
% 2.85/0.99      | k1_relset_1(X0,X1,sK4) = X0
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.99      | k1_xboole_0 = X1 ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_356]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_763,plain,
% 2.85/0.99      ( k1_relset_1(X0,X1,sK4) = X0
% 2.85/0.99      | k1_enumset1(sK1,sK1,sK1) != X0
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.99      | sK4 != sK4
% 2.85/0.99      | sK2 != X1
% 2.85/0.99      | k1_xboole_0 = X1 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_357]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_764,plain,
% 2.85/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.85/0.99      | k1_xboole_0 = sK2 ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_763]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_20,negated_conjecture,
% 2.85/0.99      ( k1_xboole_0 != sK2 ),
% 2.85/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_765,plain,
% 2.85/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.85/0.99      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 2.85/0.99      inference(global_propositional_subsumption,[status(thm)],[c_764,c_20]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_766,plain,
% 2.85/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.85/0.99      inference(renaming,[status(thm)],[c_765]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_824,plain,
% 2.85/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 2.85/0.99      inference(equality_resolution_simp,[status(thm)],[c_766]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_11,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_401,plain,
% 2.85/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.99      | sK4 != X2 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_402,plain,
% 2.85/0.99      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1482,plain,
% 2.85/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
% 2.85/0.99      inference(equality_resolution,[status(thm)],[c_402]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1550,plain,
% 2.85/0.99      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 2.85/0.99      inference(light_normalisation,[status(thm)],[c_824,c_1482]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4,plain,
% 2.85/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 2.85/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1352,plain,
% 2.85/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1627,plain,
% 2.85/0.99      ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1550,c_1352]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_10,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_410,plain,
% 2.85/0.99      ( v1_relat_1(X0)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.85/0.99      | sK4 != X0 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_411,plain,
% 2.85/0.99      ( v1_relat_1(sK4)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_9,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.99      | ~ v1_funct_1(X1)
% 2.85/0.99      | ~ v1_relat_1(X1)
% 2.85/0.99      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_23,negated_conjecture,
% 2.85/0.99      ( v1_funct_1(sK4) ),
% 2.85/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_280,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.85/0.99      | ~ v1_relat_1(X1)
% 2.85/0.99      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 2.85/0.99      | sK4 != X1 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_281,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.85/0.99      | ~ v1_relat_1(sK4)
% 2.85/0.99      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_522,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.85/0.99      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.85/0.99      inference(resolution,[status(thm)],[c_411,c_281]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1062,plain,
% 2.85/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.85/0.99      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.85/0.99      | ~ sP3_iProver_split ),
% 2.85/0.99      inference(splitting,
% 2.85/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.85/0.99                [c_522]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1348,plain,
% 2.85/0.99      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.85/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.85/0.99      | sP3_iProver_split != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1062]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1063,plain,
% 2.85/0.99      ( sP3_iProver_split | sP0_iProver_split ),
% 2.85/0.99      inference(splitting,
% 2.85/0.99                [splitting(split),new_symbols(definition,[])],
% 2.85/0.99                [c_522]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1105,plain,
% 2.85/0.99      ( sP3_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1106,plain,
% 2.85/0.99      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.85/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.85/0.99      | sP3_iProver_split != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1062]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1065,plain,( X0 = X0 ),theory(equality) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1483,plain,
% 2.85/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_1065]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_6,plain,
% 2.85/0.99      ( ~ v1_relat_1(X0)
% 2.85/0.99      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.85/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_557,plain,
% 2.85/0.99      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.85/0.99      | sK4 != X0 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_411]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_558,plain,
% 2.85/0.99      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_557]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1057,plain,
% 2.85/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.99      | ~ sP0_iProver_split ),
% 2.85/0.99      inference(splitting,
% 2.85/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.85/0.99                [c_558]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1484,plain,
% 2.85/0.99      ( ~ sP0_iProver_split
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_1057]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1489,plain,
% 2.85/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.85/0.99      | sP0_iProver_split != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1484]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2932,plain,
% 2.85/0.99      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.85/0.99      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_1348,c_1105,c_1106,c_1483,c_1489]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2933,plain,
% 2.85/0.99      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.85/0.99      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.85/0.99      inference(renaming,[status(thm)],[c_2932]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2941,plain,
% 2.85/0.99      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1627,c_2933]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1058,plain,
% 2.85/0.99      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.85/0.99      | ~ sP1_iProver_split ),
% 2.85/0.99      inference(splitting,
% 2.85/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.85/0.99                [c_558]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1342,plain,
% 2.85/0.99      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.85/0.99      | sP1_iProver_split != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1059,plain,
% 2.85/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 2.85/0.99      inference(splitting,
% 2.85/0.99                [splitting(split),new_symbols(definition,[])],
% 2.85/0.99                [c_558]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2291,plain,
% 2.85/0.99      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_1342,c_1059,c_1058,c_1483,c_1484]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2295,plain,
% 2.85/0.99      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
% 2.85/0.99      inference(superposition,[status(thm)],[c_1550,c_2291]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_8,plain,
% 2.85/0.99      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_536,plain,
% 2.85/0.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.85/0.99      | sK4 != X0 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_411]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_537,plain,
% 2.85/0.99      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_536]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1485,plain,
% 2.85/0.99      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.85/0.99      inference(instantiation,[status(thm)],[c_537]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1622,plain,
% 2.85/0.99      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_537,c_1483,c_1485]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2300,plain,
% 2.85/0.99      ( k11_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 2.85/0.99      inference(light_normalisation,[status(thm)],[c_2295,c_1622]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2943,plain,
% 2.85/0.99      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
% 2.85/0.99      inference(light_normalisation,[status(thm)],[c_2941,c_2300]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_19,negated_conjecture,
% 2.85/0.99      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 2.85/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1350,plain,
% 2.85/0.99      ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1555,plain,
% 2.85/0.99      ( r1_tarski(k7_relset_1(k1_relat_1(sK4),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.85/0.99      inference(demodulation,[status(thm)],[c_1550,c_1350]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_12,plain,
% 2.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.85/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.85/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_392,plain,
% 2.85/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.85/0.99      | sK4 != X2 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_393,plain,
% 2.85/0.99      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_392]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1495,plain,
% 2.85/0.99      ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.85/0.99      inference(equality_resolution,[status(thm)],[c_393]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1759,plain,
% 2.85/0.99      ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.85/0.99      inference(light_normalisation,[status(thm)],[c_1495,c_1550]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1855,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.85/0.99      inference(demodulation,[status(thm)],[c_1555,c_1759]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_3333,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 2.85/0.99      inference(demodulation,[status(thm)],[c_2943,c_1855]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_7,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.85/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_545,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.85/0.99      | sK4 != X0 ),
% 2.85/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_411]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_546,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4))
% 2.85/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.85/0.99      inference(unflattening,[status(thm)],[c_545]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1060,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) | ~ sP2_iProver_split ),
% 2.85/0.99      inference(splitting,
% 2.85/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.85/0.99                [c_546]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1345,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.85/0.99      | sP2_iProver_split != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1060]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1061,plain,
% 2.85/0.99      ( sP2_iProver_split | sP0_iProver_split ),
% 2.85/0.99      inference(splitting,
% 2.85/0.99                [splitting(split),new_symbols(definition,[])],
% 2.85/0.99                [c_546]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1100,plain,
% 2.85/0.99      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1061]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_1101,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 2.85/0.99      | sP2_iProver_split != iProver_top ),
% 2.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1060]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_2172,plain,
% 2.85/0.99      ( r1_tarski(k9_relat_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.85/0.99      inference(global_propositional_subsumption,
% 2.85/0.99                [status(thm)],
% 2.85/0.99                [c_1345,c_1100,c_1101,c_1483,c_1489]) ).
% 2.85/0.99  
% 2.85/0.99  cnf(c_4864,plain,
% 2.85/0.99      ( $false ),
% 2.85/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3333,c_2172]) ).
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/0.99  
% 2.85/0.99  ------                               Statistics
% 2.85/0.99  
% 2.85/0.99  ------ General
% 2.85/0.99  
% 2.85/0.99  abstr_ref_over_cycles:                  0
% 2.85/0.99  abstr_ref_under_cycles:                 0
% 2.85/0.99  gc_basic_clause_elim:                   0
% 2.85/0.99  forced_gc_time:                         0
% 2.85/0.99  parsing_time:                           0.012
% 2.85/0.99  unif_index_cands_time:                  0.
% 2.85/0.99  unif_index_add_time:                    0.
% 2.85/0.99  orderings_time:                         0.
% 2.85/0.99  out_proof_time:                         0.012
% 2.85/0.99  total_time:                             0.199
% 2.85/0.99  num_of_symbols:                         57
% 2.85/0.99  num_of_terms:                           5038
% 2.85/0.99  
% 2.85/0.99  ------ Preprocessing
% 2.85/0.99  
% 2.85/0.99  num_of_splits:                          6
% 2.85/0.99  num_of_split_atoms:                     4
% 2.85/0.99  num_of_reused_defs:                     2
% 2.85/0.99  num_eq_ax_congr_red:                    19
% 2.85/0.99  num_of_sem_filtered_clauses:            1
% 2.85/0.99  num_of_subtypes:                        0
% 2.85/0.99  monotx_restored_types:                  0
% 2.85/0.99  sat_num_of_epr_types:                   0
% 2.85/0.99  sat_num_of_non_cyclic_types:            0
% 2.85/0.99  sat_guarded_non_collapsed_types:        0
% 2.85/0.99  num_pure_diseq_elim:                    0
% 2.85/0.99  simp_replaced_by:                       0
% 2.85/0.99  res_preprocessed:                       112
% 2.85/0.99  prep_upred:                             0
% 2.85/0.99  prep_unflattend:                        54
% 2.85/0.99  smt_new_axioms:                         0
% 2.85/0.99  pred_elim_cands:                        2
% 2.85/0.99  pred_elim:                              4
% 2.85/0.99  pred_elim_cl:                           7
% 2.85/0.99  pred_elim_cycles:                       11
% 2.85/0.99  merged_defs:                            0
% 2.85/0.99  merged_defs_ncl:                        0
% 2.85/0.99  bin_hyper_res:                          0
% 2.85/0.99  prep_cycles:                            4
% 2.85/0.99  pred_elim_time:                         0.014
% 2.85/0.99  splitting_time:                         0.
% 2.85/0.99  sem_filter_time:                        0.
% 2.85/0.99  monotx_time:                            0.
% 2.85/0.99  subtype_inf_time:                       0.
% 2.85/0.99  
% 2.85/0.99  ------ Problem properties
% 2.85/0.99  
% 2.85/0.99  clauses:                                23
% 2.85/0.99  conjectures:                            2
% 2.85/0.99  epr:                                    4
% 2.85/0.99  horn:                                   17
% 2.85/0.99  ground:                                 8
% 2.85/0.99  unary:                                  5
% 2.85/0.99  binary:                                 11
% 2.85/0.99  lits:                                   50
% 2.85/0.99  lits_eq:                                29
% 2.85/0.99  fd_pure:                                0
% 2.85/0.99  fd_pseudo:                              0
% 2.85/0.99  fd_cond:                                0
% 2.85/0.99  fd_pseudo_cond:                         3
% 2.85/0.99  ac_symbols:                             0
% 2.85/0.99  
% 2.85/0.99  ------ Propositional Solver
% 2.85/0.99  
% 2.85/0.99  prop_solver_calls:                      27
% 2.85/0.99  prop_fast_solver_calls:                 783
% 2.85/0.99  smt_solver_calls:                       0
% 2.85/0.99  smt_fast_solver_calls:                  0
% 2.85/0.99  prop_num_of_clauses:                    1393
% 2.85/0.99  prop_preprocess_simplified:             4992
% 2.85/0.99  prop_fo_subsumed:                       12
% 2.85/0.99  prop_solver_time:                       0.
% 2.85/0.99  smt_solver_time:                        0.
% 2.85/0.99  smt_fast_solver_time:                   0.
% 2.85/0.99  prop_fast_solver_time:                  0.
% 2.85/0.99  prop_unsat_core_time:                   0.
% 2.85/0.99  
% 2.85/0.99  ------ QBF
% 2.85/0.99  
% 2.85/0.99  qbf_q_res:                              0
% 2.85/0.99  qbf_num_tautologies:                    0
% 2.85/0.99  qbf_prep_cycles:                        0
% 2.85/0.99  
% 2.85/0.99  ------ BMC1
% 2.85/0.99  
% 2.85/0.99  bmc1_current_bound:                     -1
% 2.85/0.99  bmc1_last_solved_bound:                 -1
% 2.85/0.99  bmc1_unsat_core_size:                   -1
% 2.85/0.99  bmc1_unsat_core_parents_size:           -1
% 2.85/0.99  bmc1_merge_next_fun:                    0
% 2.85/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.85/0.99  
% 2.85/0.99  ------ Instantiation
% 2.85/0.99  
% 2.85/0.99  inst_num_of_clauses:                    425
% 2.85/0.99  inst_num_in_passive:                    126
% 2.85/0.99  inst_num_in_active:                     200
% 2.85/0.99  inst_num_in_unprocessed:                99
% 2.85/0.99  inst_num_of_loops:                      210
% 2.85/0.99  inst_num_of_learning_restarts:          0
% 2.85/0.99  inst_num_moves_active_passive:          8
% 2.85/0.99  inst_lit_activity:                      0
% 2.85/0.99  inst_lit_activity_moves:                0
% 2.85/0.99  inst_num_tautologies:                   0
% 2.85/0.99  inst_num_prop_implied:                  0
% 2.85/0.99  inst_num_existing_simplified:           0
% 2.85/0.99  inst_num_eq_res_simplified:             0
% 2.85/0.99  inst_num_child_elim:                    0
% 2.85/0.99  inst_num_of_dismatching_blockings:      176
% 2.85/0.99  inst_num_of_non_proper_insts:           533
% 2.85/0.99  inst_num_of_duplicates:                 0
% 2.85/0.99  inst_inst_num_from_inst_to_res:         0
% 2.85/0.99  inst_dismatching_checking_time:         0.
% 2.85/0.99  
% 2.85/0.99  ------ Resolution
% 2.85/0.99  
% 2.85/0.99  res_num_of_clauses:                     0
% 2.85/0.99  res_num_in_passive:                     0
% 2.85/0.99  res_num_in_active:                      0
% 2.85/0.99  res_num_of_loops:                       116
% 2.85/0.99  res_forward_subset_subsumed:            101
% 2.85/0.99  res_backward_subset_subsumed:           0
% 2.85/0.99  res_forward_subsumed:                   0
% 2.85/0.99  res_backward_subsumed:                  0
% 2.85/0.99  res_forward_subsumption_resolution:     0
% 2.85/0.99  res_backward_subsumption_resolution:    0
% 2.85/0.99  res_clause_to_clause_subsumption:       2390
% 2.85/0.99  res_orphan_elimination:                 0
% 2.85/0.99  res_tautology_del:                      38
% 2.85/0.99  res_num_eq_res_simplified:              1
% 2.85/0.99  res_num_sel_changes:                    0
% 2.85/0.99  res_moves_from_active_to_pass:          0
% 2.85/0.99  
% 2.85/0.99  ------ Superposition
% 2.85/0.99  
% 2.85/0.99  sup_time_total:                         0.
% 2.85/0.99  sup_time_generating:                    0.
% 2.85/0.99  sup_time_sim_full:                      0.
% 2.85/0.99  sup_time_sim_immed:                     0.
% 2.85/0.99  
% 2.85/0.99  sup_num_of_clauses:                     99
% 2.85/0.99  sup_num_in_active:                      34
% 2.85/0.99  sup_num_in_passive:                     65
% 2.85/0.99  sup_num_of_loops:                       40
% 2.85/0.99  sup_fw_superposition:                   64
% 2.85/0.99  sup_bw_superposition:                   93
% 2.85/0.99  sup_immediate_simplified:               49
% 2.85/0.99  sup_given_eliminated:                   0
% 2.85/0.99  comparisons_done:                       0
% 2.85/0.99  comparisons_avoided:                    23
% 2.85/0.99  
% 2.85/0.99  ------ Simplifications
% 2.85/0.99  
% 2.85/0.99  
% 2.85/0.99  sim_fw_subset_subsumed:                 12
% 2.85/0.99  sim_bw_subset_subsumed:                 0
% 2.85/0.99  sim_fw_subsumed:                        21
% 2.85/0.99  sim_bw_subsumed:                        2
% 2.85/0.99  sim_fw_subsumption_res:                 4
% 2.85/0.99  sim_bw_subsumption_res:                 0
% 2.85/0.99  sim_tautology_del:                      0
% 2.85/0.99  sim_eq_tautology_del:                   3
% 2.85/0.99  sim_eq_res_simp:                        0
% 2.85/0.99  sim_fw_demodulated:                     1
% 2.85/0.99  sim_bw_demodulated:                     6
% 2.85/0.99  sim_light_normalised:                   13
% 2.85/0.99  sim_joinable_taut:                      0
% 2.85/0.99  sim_joinable_simp:                      0
% 2.85/0.99  sim_ac_normalised:                      0
% 2.85/0.99  sim_smt_subsumption:                    0
% 2.85/0.99  
%------------------------------------------------------------------------------
