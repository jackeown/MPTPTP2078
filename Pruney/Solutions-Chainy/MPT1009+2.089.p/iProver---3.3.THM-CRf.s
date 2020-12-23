%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:46 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 727 expanded)
%              Number of clauses        :   67 ( 174 expanded)
%              Number of leaves         :   15 ( 176 expanded)
%              Depth                    :   19
%              Number of atoms          :  365 (1918 expanded)
%              Number of equality atoms :  210 ( 802 expanded)
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

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f31,plain,
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

fof(f32,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f31])).

fof(f55,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f71,plain,(
    v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f55,f60])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f30,plain,(
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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f57,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f74,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f75,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f74])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f58,f60,f60])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_331,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_332,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_726,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | sK2 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_332])).

cnf(c_727,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_728,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_727,c_19])).

cnf(c_729,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_728])).

cnf(c_787,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_729])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_376,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_377,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_1438,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_377])).

cnf(c_1550,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_787,c_1438])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1312,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1580,plain,
    ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1312])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_385,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_386,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_268,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_269,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_497,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_386,c_269])).

cnf(c_1024,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_497])).

cnf(c_1308,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_1025,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_497])).

cnf(c_1065,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1025])).

cnf(c_1066,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_1027,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1439,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_523,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_386])).

cnf(c_524,plain,
    ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_1019,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_524])).

cnf(c_1440,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1444,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1440])).

cnf(c_2616,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1308,c_1065,c_1066,c_1439,c_1444])).

cnf(c_2617,plain,
    ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2616])).

cnf(c_2625,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1580,c_2617])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_367,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_368,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1456,plain,
    ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_368])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1310,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1515,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1456,c_1310])).

cnf(c_3259,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2625,c_1515])).

cnf(c_1020,plain,
    ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_524])).

cnf(c_1302,plain,
    ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0)
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_1021,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_524])).

cnf(c_2182,plain,
    ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1302,c_1021,c_1020,c_1439,c_1440])).

cnf(c_2186,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
    inference(superposition,[status(thm)],[c_1550,c_2182])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_511,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_386])).

cnf(c_512,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4)))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_1022,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4)))
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_512])).

cnf(c_1305,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4))) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_1023,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_512])).

cnf(c_1060,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_1061,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4))) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_2068,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1305,c_1060,c_1061,c_1439,c_1444])).

cnf(c_3104,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k11_relat_1(sK4,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2186,c_2068])).

cnf(c_3279,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3259,c_3104])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.77/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.01  
% 2.77/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/1.01  
% 2.77/1.01  ------  iProver source info
% 2.77/1.01  
% 2.77/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.77/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/1.01  git: non_committed_changes: false
% 2.77/1.01  git: last_make_outside_of_git: false
% 2.77/1.01  
% 2.77/1.01  ------ 
% 2.77/1.01  
% 2.77/1.01  ------ Input Options
% 2.77/1.01  
% 2.77/1.01  --out_options                           all
% 2.77/1.01  --tptp_safe_out                         true
% 2.77/1.01  --problem_path                          ""
% 2.77/1.01  --include_path                          ""
% 2.77/1.01  --clausifier                            res/vclausify_rel
% 2.77/1.01  --clausifier_options                    --mode clausify
% 2.77/1.01  --stdin                                 false
% 2.77/1.01  --stats_out                             all
% 2.77/1.01  
% 2.77/1.01  ------ General Options
% 2.77/1.01  
% 2.77/1.01  --fof                                   false
% 2.77/1.01  --time_out_real                         305.
% 2.77/1.01  --time_out_virtual                      -1.
% 2.77/1.01  --symbol_type_check                     false
% 2.77/1.01  --clausify_out                          false
% 2.77/1.01  --sig_cnt_out                           false
% 2.77/1.01  --trig_cnt_out                          false
% 2.77/1.01  --trig_cnt_out_tolerance                1.
% 2.77/1.01  --trig_cnt_out_sk_spl                   false
% 2.77/1.01  --abstr_cl_out                          false
% 2.77/1.01  
% 2.77/1.01  ------ Global Options
% 2.77/1.01  
% 2.77/1.01  --schedule                              default
% 2.77/1.01  --add_important_lit                     false
% 2.77/1.01  --prop_solver_per_cl                    1000
% 2.77/1.01  --min_unsat_core                        false
% 2.77/1.01  --soft_assumptions                      false
% 2.77/1.01  --soft_lemma_size                       3
% 2.77/1.01  --prop_impl_unit_size                   0
% 2.77/1.01  --prop_impl_unit                        []
% 2.77/1.01  --share_sel_clauses                     true
% 2.77/1.01  --reset_solvers                         false
% 2.77/1.01  --bc_imp_inh                            [conj_cone]
% 2.77/1.01  --conj_cone_tolerance                   3.
% 2.77/1.01  --extra_neg_conj                        none
% 2.77/1.01  --large_theory_mode                     true
% 2.77/1.01  --prolific_symb_bound                   200
% 2.77/1.01  --lt_threshold                          2000
% 2.77/1.01  --clause_weak_htbl                      true
% 2.77/1.01  --gc_record_bc_elim                     false
% 2.77/1.01  
% 2.77/1.01  ------ Preprocessing Options
% 2.77/1.01  
% 2.77/1.01  --preprocessing_flag                    true
% 2.77/1.01  --time_out_prep_mult                    0.1
% 2.77/1.01  --splitting_mode                        input
% 2.77/1.01  --splitting_grd                         true
% 2.77/1.01  --splitting_cvd                         false
% 2.77/1.01  --splitting_cvd_svl                     false
% 2.77/1.01  --splitting_nvd                         32
% 2.77/1.01  --sub_typing                            true
% 2.77/1.01  --prep_gs_sim                           true
% 2.77/1.01  --prep_unflatten                        true
% 2.77/1.01  --prep_res_sim                          true
% 2.77/1.01  --prep_upred                            true
% 2.77/1.01  --prep_sem_filter                       exhaustive
% 2.77/1.01  --prep_sem_filter_out                   false
% 2.77/1.01  --pred_elim                             true
% 2.77/1.01  --res_sim_input                         true
% 2.77/1.01  --eq_ax_congr_red                       true
% 2.77/1.01  --pure_diseq_elim                       true
% 2.77/1.01  --brand_transform                       false
% 2.77/1.01  --non_eq_to_eq                          false
% 2.77/1.01  --prep_def_merge                        true
% 2.77/1.01  --prep_def_merge_prop_impl              false
% 2.77/1.01  --prep_def_merge_mbd                    true
% 2.77/1.01  --prep_def_merge_tr_red                 false
% 2.77/1.01  --prep_def_merge_tr_cl                  false
% 2.77/1.01  --smt_preprocessing                     true
% 2.77/1.01  --smt_ac_axioms                         fast
% 2.77/1.01  --preprocessed_out                      false
% 2.77/1.01  --preprocessed_stats                    false
% 2.77/1.01  
% 2.77/1.01  ------ Abstraction refinement Options
% 2.77/1.01  
% 2.77/1.01  --abstr_ref                             []
% 2.77/1.01  --abstr_ref_prep                        false
% 2.77/1.01  --abstr_ref_until_sat                   false
% 2.77/1.01  --abstr_ref_sig_restrict                funpre
% 2.77/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.01  --abstr_ref_under                       []
% 2.77/1.01  
% 2.77/1.01  ------ SAT Options
% 2.77/1.01  
% 2.77/1.01  --sat_mode                              false
% 2.77/1.01  --sat_fm_restart_options                ""
% 2.77/1.01  --sat_gr_def                            false
% 2.77/1.01  --sat_epr_types                         true
% 2.77/1.01  --sat_non_cyclic_types                  false
% 2.77/1.01  --sat_finite_models                     false
% 2.77/1.01  --sat_fm_lemmas                         false
% 2.77/1.01  --sat_fm_prep                           false
% 2.77/1.01  --sat_fm_uc_incr                        true
% 2.77/1.01  --sat_out_model                         small
% 2.77/1.01  --sat_out_clauses                       false
% 2.77/1.01  
% 2.77/1.01  ------ QBF Options
% 2.77/1.01  
% 2.77/1.01  --qbf_mode                              false
% 2.77/1.01  --qbf_elim_univ                         false
% 2.77/1.01  --qbf_dom_inst                          none
% 2.77/1.01  --qbf_dom_pre_inst                      false
% 2.77/1.01  --qbf_sk_in                             false
% 2.77/1.01  --qbf_pred_elim                         true
% 2.77/1.01  --qbf_split                             512
% 2.77/1.01  
% 2.77/1.01  ------ BMC1 Options
% 2.77/1.01  
% 2.77/1.01  --bmc1_incremental                      false
% 2.77/1.01  --bmc1_axioms                           reachable_all
% 2.77/1.01  --bmc1_min_bound                        0
% 2.77/1.01  --bmc1_max_bound                        -1
% 2.77/1.01  --bmc1_max_bound_default                -1
% 2.77/1.01  --bmc1_symbol_reachability              true
% 2.77/1.01  --bmc1_property_lemmas                  false
% 2.77/1.01  --bmc1_k_induction                      false
% 2.77/1.01  --bmc1_non_equiv_states                 false
% 2.77/1.01  --bmc1_deadlock                         false
% 2.77/1.01  --bmc1_ucm                              false
% 2.77/1.01  --bmc1_add_unsat_core                   none
% 2.77/1.02  --bmc1_unsat_core_children              false
% 2.77/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.02  --bmc1_out_stat                         full
% 2.77/1.02  --bmc1_ground_init                      false
% 2.77/1.02  --bmc1_pre_inst_next_state              false
% 2.77/1.02  --bmc1_pre_inst_state                   false
% 2.77/1.02  --bmc1_pre_inst_reach_state             false
% 2.77/1.02  --bmc1_out_unsat_core                   false
% 2.77/1.02  --bmc1_aig_witness_out                  false
% 2.77/1.02  --bmc1_verbose                          false
% 2.77/1.02  --bmc1_dump_clauses_tptp                false
% 2.77/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.02  --bmc1_dump_file                        -
% 2.77/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.02  --bmc1_ucm_extend_mode                  1
% 2.77/1.02  --bmc1_ucm_init_mode                    2
% 2.77/1.02  --bmc1_ucm_cone_mode                    none
% 2.77/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.02  --bmc1_ucm_relax_model                  4
% 2.77/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.02  --bmc1_ucm_layered_model                none
% 2.77/1.02  --bmc1_ucm_max_lemma_size               10
% 2.77/1.02  
% 2.77/1.02  ------ AIG Options
% 2.77/1.02  
% 2.77/1.02  --aig_mode                              false
% 2.77/1.02  
% 2.77/1.02  ------ Instantiation Options
% 2.77/1.02  
% 2.77/1.02  --instantiation_flag                    true
% 2.77/1.02  --inst_sos_flag                         false
% 2.77/1.02  --inst_sos_phase                        true
% 2.77/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.02  --inst_lit_sel_side                     num_symb
% 2.77/1.02  --inst_solver_per_active                1400
% 2.77/1.02  --inst_solver_calls_frac                1.
% 2.77/1.02  --inst_passive_queue_type               priority_queues
% 2.77/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.02  --inst_passive_queues_freq              [25;2]
% 2.77/1.02  --inst_dismatching                      true
% 2.77/1.02  --inst_eager_unprocessed_to_passive     true
% 2.77/1.02  --inst_prop_sim_given                   true
% 2.77/1.02  --inst_prop_sim_new                     false
% 2.77/1.02  --inst_subs_new                         false
% 2.77/1.02  --inst_eq_res_simp                      false
% 2.77/1.02  --inst_subs_given                       false
% 2.77/1.02  --inst_orphan_elimination               true
% 2.77/1.02  --inst_learning_loop_flag               true
% 2.77/1.02  --inst_learning_start                   3000
% 2.77/1.02  --inst_learning_factor                  2
% 2.77/1.02  --inst_start_prop_sim_after_learn       3
% 2.77/1.02  --inst_sel_renew                        solver
% 2.77/1.02  --inst_lit_activity_flag                true
% 2.77/1.02  --inst_restr_to_given                   false
% 2.77/1.02  --inst_activity_threshold               500
% 2.77/1.02  --inst_out_proof                        true
% 2.77/1.02  
% 2.77/1.02  ------ Resolution Options
% 2.77/1.02  
% 2.77/1.02  --resolution_flag                       true
% 2.77/1.02  --res_lit_sel                           adaptive
% 2.77/1.02  --res_lit_sel_side                      none
% 2.77/1.02  --res_ordering                          kbo
% 2.77/1.02  --res_to_prop_solver                    active
% 2.77/1.02  --res_prop_simpl_new                    false
% 2.77/1.02  --res_prop_simpl_given                  true
% 2.77/1.02  --res_passive_queue_type                priority_queues
% 2.77/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.02  --res_passive_queues_freq               [15;5]
% 2.77/1.02  --res_forward_subs                      full
% 2.77/1.02  --res_backward_subs                     full
% 2.77/1.02  --res_forward_subs_resolution           true
% 2.77/1.02  --res_backward_subs_resolution          true
% 2.77/1.02  --res_orphan_elimination                true
% 2.77/1.02  --res_time_limit                        2.
% 2.77/1.02  --res_out_proof                         true
% 2.77/1.02  
% 2.77/1.02  ------ Superposition Options
% 2.77/1.02  
% 2.77/1.02  --superposition_flag                    true
% 2.77/1.02  --sup_passive_queue_type                priority_queues
% 2.77/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.02  --demod_completeness_check              fast
% 2.77/1.02  --demod_use_ground                      true
% 2.77/1.02  --sup_to_prop_solver                    passive
% 2.77/1.02  --sup_prop_simpl_new                    true
% 2.77/1.02  --sup_prop_simpl_given                  true
% 2.77/1.02  --sup_fun_splitting                     false
% 2.77/1.02  --sup_smt_interval                      50000
% 2.77/1.02  
% 2.77/1.02  ------ Superposition Simplification Setup
% 2.77/1.02  
% 2.77/1.02  --sup_indices_passive                   []
% 2.77/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_full_bw                           [BwDemod]
% 2.77/1.02  --sup_immed_triv                        [TrivRules]
% 2.77/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_immed_bw_main                     []
% 2.77/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.02  
% 2.77/1.02  ------ Combination Options
% 2.77/1.02  
% 2.77/1.02  --comb_res_mult                         3
% 2.77/1.02  --comb_sup_mult                         2
% 2.77/1.02  --comb_inst_mult                        10
% 2.77/1.02  
% 2.77/1.02  ------ Debug Options
% 2.77/1.02  
% 2.77/1.02  --dbg_backtrace                         false
% 2.77/1.02  --dbg_dump_prop_clauses                 false
% 2.77/1.02  --dbg_dump_prop_clauses_file            -
% 2.77/1.02  --dbg_out_stat                          false
% 2.77/1.02  ------ Parsing...
% 2.77/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/1.02  
% 2.77/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.77/1.02  
% 2.77/1.02  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/1.02  
% 2.77/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/1.02  ------ Proving...
% 2.77/1.02  ------ Problem Properties 
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  clauses                                 22
% 2.77/1.02  conjectures                             2
% 2.77/1.02  EPR                                     4
% 2.77/1.02  Horn                                    16
% 2.77/1.02  unary                                   5
% 2.77/1.02  binary                                  10
% 2.77/1.02  lits                                    48
% 2.77/1.02  lits eq                                 27
% 2.77/1.02  fd_pure                                 0
% 2.77/1.02  fd_pseudo                               0
% 2.77/1.02  fd_cond                                 0
% 2.77/1.02  fd_pseudo_cond                          3
% 2.77/1.02  AC symbols                              0
% 2.77/1.02  
% 2.77/1.02  ------ Schedule dynamic 5 is on 
% 2.77/1.02  
% 2.77/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  ------ 
% 2.77/1.02  Current options:
% 2.77/1.02  ------ 
% 2.77/1.02  
% 2.77/1.02  ------ Input Options
% 2.77/1.02  
% 2.77/1.02  --out_options                           all
% 2.77/1.02  --tptp_safe_out                         true
% 2.77/1.02  --problem_path                          ""
% 2.77/1.02  --include_path                          ""
% 2.77/1.02  --clausifier                            res/vclausify_rel
% 2.77/1.02  --clausifier_options                    --mode clausify
% 2.77/1.02  --stdin                                 false
% 2.77/1.02  --stats_out                             all
% 2.77/1.02  
% 2.77/1.02  ------ General Options
% 2.77/1.02  
% 2.77/1.02  --fof                                   false
% 2.77/1.02  --time_out_real                         305.
% 2.77/1.02  --time_out_virtual                      -1.
% 2.77/1.02  --symbol_type_check                     false
% 2.77/1.02  --clausify_out                          false
% 2.77/1.02  --sig_cnt_out                           false
% 2.77/1.02  --trig_cnt_out                          false
% 2.77/1.02  --trig_cnt_out_tolerance                1.
% 2.77/1.02  --trig_cnt_out_sk_spl                   false
% 2.77/1.02  --abstr_cl_out                          false
% 2.77/1.02  
% 2.77/1.02  ------ Global Options
% 2.77/1.02  
% 2.77/1.02  --schedule                              default
% 2.77/1.02  --add_important_lit                     false
% 2.77/1.02  --prop_solver_per_cl                    1000
% 2.77/1.02  --min_unsat_core                        false
% 2.77/1.02  --soft_assumptions                      false
% 2.77/1.02  --soft_lemma_size                       3
% 2.77/1.02  --prop_impl_unit_size                   0
% 2.77/1.02  --prop_impl_unit                        []
% 2.77/1.02  --share_sel_clauses                     true
% 2.77/1.02  --reset_solvers                         false
% 2.77/1.02  --bc_imp_inh                            [conj_cone]
% 2.77/1.02  --conj_cone_tolerance                   3.
% 2.77/1.02  --extra_neg_conj                        none
% 2.77/1.02  --large_theory_mode                     true
% 2.77/1.02  --prolific_symb_bound                   200
% 2.77/1.02  --lt_threshold                          2000
% 2.77/1.02  --clause_weak_htbl                      true
% 2.77/1.02  --gc_record_bc_elim                     false
% 2.77/1.02  
% 2.77/1.02  ------ Preprocessing Options
% 2.77/1.02  
% 2.77/1.02  --preprocessing_flag                    true
% 2.77/1.02  --time_out_prep_mult                    0.1
% 2.77/1.02  --splitting_mode                        input
% 2.77/1.02  --splitting_grd                         true
% 2.77/1.02  --splitting_cvd                         false
% 2.77/1.02  --splitting_cvd_svl                     false
% 2.77/1.02  --splitting_nvd                         32
% 2.77/1.02  --sub_typing                            true
% 2.77/1.02  --prep_gs_sim                           true
% 2.77/1.02  --prep_unflatten                        true
% 2.77/1.02  --prep_res_sim                          true
% 2.77/1.02  --prep_upred                            true
% 2.77/1.02  --prep_sem_filter                       exhaustive
% 2.77/1.02  --prep_sem_filter_out                   false
% 2.77/1.02  --pred_elim                             true
% 2.77/1.02  --res_sim_input                         true
% 2.77/1.02  --eq_ax_congr_red                       true
% 2.77/1.02  --pure_diseq_elim                       true
% 2.77/1.02  --brand_transform                       false
% 2.77/1.02  --non_eq_to_eq                          false
% 2.77/1.02  --prep_def_merge                        true
% 2.77/1.02  --prep_def_merge_prop_impl              false
% 2.77/1.02  --prep_def_merge_mbd                    true
% 2.77/1.02  --prep_def_merge_tr_red                 false
% 2.77/1.02  --prep_def_merge_tr_cl                  false
% 2.77/1.02  --smt_preprocessing                     true
% 2.77/1.02  --smt_ac_axioms                         fast
% 2.77/1.02  --preprocessed_out                      false
% 2.77/1.02  --preprocessed_stats                    false
% 2.77/1.02  
% 2.77/1.02  ------ Abstraction refinement Options
% 2.77/1.02  
% 2.77/1.02  --abstr_ref                             []
% 2.77/1.02  --abstr_ref_prep                        false
% 2.77/1.02  --abstr_ref_until_sat                   false
% 2.77/1.02  --abstr_ref_sig_restrict                funpre
% 2.77/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/1.02  --abstr_ref_under                       []
% 2.77/1.02  
% 2.77/1.02  ------ SAT Options
% 2.77/1.02  
% 2.77/1.02  --sat_mode                              false
% 2.77/1.02  --sat_fm_restart_options                ""
% 2.77/1.02  --sat_gr_def                            false
% 2.77/1.02  --sat_epr_types                         true
% 2.77/1.02  --sat_non_cyclic_types                  false
% 2.77/1.02  --sat_finite_models                     false
% 2.77/1.02  --sat_fm_lemmas                         false
% 2.77/1.02  --sat_fm_prep                           false
% 2.77/1.02  --sat_fm_uc_incr                        true
% 2.77/1.02  --sat_out_model                         small
% 2.77/1.02  --sat_out_clauses                       false
% 2.77/1.02  
% 2.77/1.02  ------ QBF Options
% 2.77/1.02  
% 2.77/1.02  --qbf_mode                              false
% 2.77/1.02  --qbf_elim_univ                         false
% 2.77/1.02  --qbf_dom_inst                          none
% 2.77/1.02  --qbf_dom_pre_inst                      false
% 2.77/1.02  --qbf_sk_in                             false
% 2.77/1.02  --qbf_pred_elim                         true
% 2.77/1.02  --qbf_split                             512
% 2.77/1.02  
% 2.77/1.02  ------ BMC1 Options
% 2.77/1.02  
% 2.77/1.02  --bmc1_incremental                      false
% 2.77/1.02  --bmc1_axioms                           reachable_all
% 2.77/1.02  --bmc1_min_bound                        0
% 2.77/1.02  --bmc1_max_bound                        -1
% 2.77/1.02  --bmc1_max_bound_default                -1
% 2.77/1.02  --bmc1_symbol_reachability              true
% 2.77/1.02  --bmc1_property_lemmas                  false
% 2.77/1.02  --bmc1_k_induction                      false
% 2.77/1.02  --bmc1_non_equiv_states                 false
% 2.77/1.02  --bmc1_deadlock                         false
% 2.77/1.02  --bmc1_ucm                              false
% 2.77/1.02  --bmc1_add_unsat_core                   none
% 2.77/1.02  --bmc1_unsat_core_children              false
% 2.77/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/1.02  --bmc1_out_stat                         full
% 2.77/1.02  --bmc1_ground_init                      false
% 2.77/1.02  --bmc1_pre_inst_next_state              false
% 2.77/1.02  --bmc1_pre_inst_state                   false
% 2.77/1.02  --bmc1_pre_inst_reach_state             false
% 2.77/1.02  --bmc1_out_unsat_core                   false
% 2.77/1.02  --bmc1_aig_witness_out                  false
% 2.77/1.02  --bmc1_verbose                          false
% 2.77/1.02  --bmc1_dump_clauses_tptp                false
% 2.77/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.77/1.02  --bmc1_dump_file                        -
% 2.77/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.77/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.77/1.02  --bmc1_ucm_extend_mode                  1
% 2.77/1.02  --bmc1_ucm_init_mode                    2
% 2.77/1.02  --bmc1_ucm_cone_mode                    none
% 2.77/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.77/1.02  --bmc1_ucm_relax_model                  4
% 2.77/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.77/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/1.02  --bmc1_ucm_layered_model                none
% 2.77/1.02  --bmc1_ucm_max_lemma_size               10
% 2.77/1.02  
% 2.77/1.02  ------ AIG Options
% 2.77/1.02  
% 2.77/1.02  --aig_mode                              false
% 2.77/1.02  
% 2.77/1.02  ------ Instantiation Options
% 2.77/1.02  
% 2.77/1.02  --instantiation_flag                    true
% 2.77/1.02  --inst_sos_flag                         false
% 2.77/1.02  --inst_sos_phase                        true
% 2.77/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/1.02  --inst_lit_sel_side                     none
% 2.77/1.02  --inst_solver_per_active                1400
% 2.77/1.02  --inst_solver_calls_frac                1.
% 2.77/1.02  --inst_passive_queue_type               priority_queues
% 2.77/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/1.02  --inst_passive_queues_freq              [25;2]
% 2.77/1.02  --inst_dismatching                      true
% 2.77/1.02  --inst_eager_unprocessed_to_passive     true
% 2.77/1.02  --inst_prop_sim_given                   true
% 2.77/1.02  --inst_prop_sim_new                     false
% 2.77/1.02  --inst_subs_new                         false
% 2.77/1.02  --inst_eq_res_simp                      false
% 2.77/1.02  --inst_subs_given                       false
% 2.77/1.02  --inst_orphan_elimination               true
% 2.77/1.02  --inst_learning_loop_flag               true
% 2.77/1.02  --inst_learning_start                   3000
% 2.77/1.02  --inst_learning_factor                  2
% 2.77/1.02  --inst_start_prop_sim_after_learn       3
% 2.77/1.02  --inst_sel_renew                        solver
% 2.77/1.02  --inst_lit_activity_flag                true
% 2.77/1.02  --inst_restr_to_given                   false
% 2.77/1.02  --inst_activity_threshold               500
% 2.77/1.02  --inst_out_proof                        true
% 2.77/1.02  
% 2.77/1.02  ------ Resolution Options
% 2.77/1.02  
% 2.77/1.02  --resolution_flag                       false
% 2.77/1.02  --res_lit_sel                           adaptive
% 2.77/1.02  --res_lit_sel_side                      none
% 2.77/1.02  --res_ordering                          kbo
% 2.77/1.02  --res_to_prop_solver                    active
% 2.77/1.02  --res_prop_simpl_new                    false
% 2.77/1.02  --res_prop_simpl_given                  true
% 2.77/1.02  --res_passive_queue_type                priority_queues
% 2.77/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/1.02  --res_passive_queues_freq               [15;5]
% 2.77/1.02  --res_forward_subs                      full
% 2.77/1.02  --res_backward_subs                     full
% 2.77/1.02  --res_forward_subs_resolution           true
% 2.77/1.02  --res_backward_subs_resolution          true
% 2.77/1.02  --res_orphan_elimination                true
% 2.77/1.02  --res_time_limit                        2.
% 2.77/1.02  --res_out_proof                         true
% 2.77/1.02  
% 2.77/1.02  ------ Superposition Options
% 2.77/1.02  
% 2.77/1.02  --superposition_flag                    true
% 2.77/1.02  --sup_passive_queue_type                priority_queues
% 2.77/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.77/1.02  --demod_completeness_check              fast
% 2.77/1.02  --demod_use_ground                      true
% 2.77/1.02  --sup_to_prop_solver                    passive
% 2.77/1.02  --sup_prop_simpl_new                    true
% 2.77/1.02  --sup_prop_simpl_given                  true
% 2.77/1.02  --sup_fun_splitting                     false
% 2.77/1.02  --sup_smt_interval                      50000
% 2.77/1.02  
% 2.77/1.02  ------ Superposition Simplification Setup
% 2.77/1.02  
% 2.77/1.02  --sup_indices_passive                   []
% 2.77/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.77/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_full_bw                           [BwDemod]
% 2.77/1.02  --sup_immed_triv                        [TrivRules]
% 2.77/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_immed_bw_main                     []
% 2.77/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.77/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.77/1.02  
% 2.77/1.02  ------ Combination Options
% 2.77/1.02  
% 2.77/1.02  --comb_res_mult                         3
% 2.77/1.02  --comb_sup_mult                         2
% 2.77/1.02  --comb_inst_mult                        10
% 2.77/1.02  
% 2.77/1.02  ------ Debug Options
% 2.77/1.02  
% 2.77/1.02  --dbg_backtrace                         false
% 2.77/1.02  --dbg_dump_prop_clauses                 false
% 2.77/1.02  --dbg_dump_prop_clauses_file            -
% 2.77/1.02  --dbg_out_stat                          false
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  ------ Proving...
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  % SZS status Theorem for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02   Resolution empty clause
% 2.77/1.02  
% 2.77/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02  fof(f12,conjecture,(
% 2.77/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f13,negated_conjecture,(
% 2.77/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.77/1.02    inference(negated_conjecture,[],[f12])).
% 2.77/1.02  
% 2.77/1.02  fof(f23,plain,(
% 2.77/1.02    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.77/1.02    inference(ennf_transformation,[],[f13])).
% 2.77/1.02  
% 2.77/1.02  fof(f24,plain,(
% 2.77/1.02    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.77/1.02    inference(flattening,[],[f23])).
% 2.77/1.02  
% 2.77/1.02  fof(f31,plain,(
% 2.77/1.02    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f32,plain,(
% 2.77/1.02    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 2.77/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f31])).
% 2.77/1.02  
% 2.77/1.02  fof(f55,plain,(
% 2.77/1.02    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 2.77/1.02    inference(cnf_transformation,[],[f32])).
% 2.77/1.02  
% 2.77/1.02  fof(f2,axiom,(
% 2.77/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f39,plain,(
% 2.77/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f2])).
% 2.77/1.02  
% 2.77/1.02  fof(f3,axiom,(
% 2.77/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f40,plain,(
% 2.77/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f3])).
% 2.77/1.02  
% 2.77/1.02  fof(f4,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f41,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f4])).
% 2.77/1.02  
% 2.77/1.02  fof(f59,plain,(
% 2.77/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.77/1.02    inference(definition_unfolding,[],[f40,f41])).
% 2.77/1.02  
% 2.77/1.02  fof(f60,plain,(
% 2.77/1.02    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.77/1.02    inference(definition_unfolding,[],[f39,f59])).
% 2.77/1.02  
% 2.77/1.02  fof(f71,plain,(
% 2.77/1.02    v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 2.77/1.02    inference(definition_unfolding,[],[f55,f60])).
% 2.77/1.02  
% 2.77/1.02  fof(f11,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f21,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(ennf_transformation,[],[f11])).
% 2.77/1.02  
% 2.77/1.02  fof(f22,plain,(
% 2.77/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(flattening,[],[f21])).
% 2.77/1.02  
% 2.77/1.02  fof(f30,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(nnf_transformation,[],[f22])).
% 2.77/1.02  
% 2.77/1.02  fof(f48,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f30])).
% 2.77/1.02  
% 2.77/1.02  fof(f56,plain,(
% 2.77/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.77/1.02    inference(cnf_transformation,[],[f32])).
% 2.77/1.02  
% 2.77/1.02  fof(f70,plain,(
% 2.77/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 2.77/1.02    inference(definition_unfolding,[],[f56,f60])).
% 2.77/1.02  
% 2.77/1.02  fof(f57,plain,(
% 2.77/1.02    k1_xboole_0 != sK2),
% 2.77/1.02    inference(cnf_transformation,[],[f32])).
% 2.77/1.02  
% 2.77/1.02  fof(f9,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f19,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(ennf_transformation,[],[f9])).
% 2.77/1.02  
% 2.77/1.02  fof(f46,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f19])).
% 2.77/1.02  
% 2.77/1.02  fof(f1,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f25,plain,(
% 2.77/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.77/1.02    inference(nnf_transformation,[],[f1])).
% 2.77/1.02  
% 2.77/1.02  fof(f26,plain,(
% 2.77/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.77/1.02    inference(flattening,[],[f25])).
% 2.77/1.02  
% 2.77/1.02  fof(f27,plain,(
% 2.77/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.77/1.02    inference(rectify,[],[f26])).
% 2.77/1.02  
% 2.77/1.02  fof(f28,plain,(
% 2.77/1.02    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.77/1.02    introduced(choice_axiom,[])).
% 2.77/1.02  
% 2.77/1.02  fof(f29,plain,(
% 2.77/1.02    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.77/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.77/1.02  
% 2.77/1.02  fof(f34,plain,(
% 2.77/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.77/1.02    inference(cnf_transformation,[],[f29])).
% 2.77/1.02  
% 2.77/1.02  fof(f65,plain,(
% 2.77/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.77/1.02    inference(definition_unfolding,[],[f34,f59])).
% 2.77/1.02  
% 2.77/1.02  fof(f74,plain,(
% 2.77/1.02    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 2.77/1.02    inference(equality_resolution,[],[f65])).
% 2.77/1.02  
% 2.77/1.02  fof(f75,plain,(
% 2.77/1.02    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 2.77/1.02    inference(equality_resolution,[],[f74])).
% 2.77/1.02  
% 2.77/1.02  fof(f8,axiom,(
% 2.77/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f18,plain,(
% 2.77/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(ennf_transformation,[],[f8])).
% 2.77/1.02  
% 2.77/1.02  fof(f45,plain,(
% 2.77/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f18])).
% 2.77/1.02  
% 2.77/1.02  fof(f7,axiom,(
% 2.77/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f16,plain,(
% 2.77/1.02    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.77/1.02    inference(ennf_transformation,[],[f7])).
% 2.77/1.02  
% 2.77/1.02  fof(f17,plain,(
% 2.77/1.02    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.77/1.02    inference(flattening,[],[f16])).
% 2.77/1.02  
% 2.77/1.02  fof(f44,plain,(
% 2.77/1.02    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f17])).
% 2.77/1.02  
% 2.77/1.02  fof(f68,plain,(
% 2.77/1.02    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.77/1.02    inference(definition_unfolding,[],[f44,f60])).
% 2.77/1.02  
% 2.77/1.02  fof(f54,plain,(
% 2.77/1.02    v1_funct_1(sK4)),
% 2.77/1.02    inference(cnf_transformation,[],[f32])).
% 2.77/1.02  
% 2.77/1.02  fof(f5,axiom,(
% 2.77/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f14,plain,(
% 2.77/1.02    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.77/1.02    inference(ennf_transformation,[],[f5])).
% 2.77/1.02  
% 2.77/1.02  fof(f42,plain,(
% 2.77/1.02    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f14])).
% 2.77/1.02  
% 2.77/1.02  fof(f67,plain,(
% 2.77/1.02    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.77/1.02    inference(definition_unfolding,[],[f42,f60])).
% 2.77/1.02  
% 2.77/1.02  fof(f10,axiom,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f20,plain,(
% 2.77/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/1.02    inference(ennf_transformation,[],[f10])).
% 2.77/1.02  
% 2.77/1.02  fof(f47,plain,(
% 2.77/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.77/1.02    inference(cnf_transformation,[],[f20])).
% 2.77/1.02  
% 2.77/1.02  fof(f58,plain,(
% 2.77/1.02    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 2.77/1.02    inference(cnf_transformation,[],[f32])).
% 2.77/1.02  
% 2.77/1.02  fof(f69,plain,(
% 2.77/1.02    ~r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 2.77/1.02    inference(definition_unfolding,[],[f58,f60,f60])).
% 2.77/1.02  
% 2.77/1.02  fof(f6,axiom,(
% 2.77/1.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 2.77/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/1.02  
% 2.77/1.02  fof(f15,plain,(
% 2.77/1.02    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.77/1.02    inference(ennf_transformation,[],[f6])).
% 2.77/1.02  
% 2.77/1.02  fof(f43,plain,(
% 2.77/1.02    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 2.77/1.02    inference(cnf_transformation,[],[f15])).
% 2.77/1.02  
% 2.77/1.02  cnf(c_21,negated_conjecture,
% 2.77/1.02      ( v1_funct_2(sK4,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 2.77/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_17,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.77/1.02      | k1_xboole_0 = X2 ),
% 2.77/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_20,negated_conjecture,
% 2.77/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_331,plain,
% 2.77/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.77/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.77/1.02      | sK4 != X0
% 2.77/1.02      | k1_xboole_0 = X2 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_332,plain,
% 2.77/1.02      ( ~ v1_funct_2(sK4,X0,X1)
% 2.77/1.02      | k1_relset_1(X0,X1,sK4) = X0
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.77/1.02      | k1_xboole_0 = X1 ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_331]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_726,plain,
% 2.77/1.02      ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
% 2.77/1.02      | k1_relset_1(X0,X1,sK4) = X0
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.77/1.02      | sK4 != sK4
% 2.77/1.02      | sK2 != X1
% 2.77/1.02      | k1_xboole_0 = X1 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_332]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_727,plain,
% 2.77/1.02      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.77/1.02      | k1_xboole_0 = sK2 ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_726]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_19,negated_conjecture,
% 2.77/1.02      ( k1_xboole_0 != sK2 ),
% 2.77/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_728,plain,
% 2.77/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.77/1.02      | k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 2.77/1.02      inference(global_propositional_subsumption,[status(thm)],[c_727,c_19]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_729,plain,
% 2.77/1.02      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.77/1.02      inference(renaming,[status(thm)],[c_728]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_787,plain,
% 2.77/1.02      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 2.77/1.02      inference(equality_resolution_simp,[status(thm)],[c_729]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_10,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_376,plain,
% 2.77/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.77/1.02      | sK4 != X2 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_377,plain,
% 2.77/1.02      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_376]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1438,plain,
% 2.77/1.02      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
% 2.77/1.02      inference(equality_resolution,[status(thm)],[c_377]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1550,plain,
% 2.77/1.02      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 2.77/1.02      inference(light_normalisation,[status(thm)],[c_787,c_1438]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_4,plain,
% 2.77/1.02      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 2.77/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1312,plain,
% 2.77/1.02      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1580,plain,
% 2.77/1.02      ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1550,c_1312]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_9,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_385,plain,
% 2.77/1.02      ( v1_relat_1(X0)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.77/1.02      | sK4 != X0 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_386,plain,
% 2.77/1.02      ( v1_relat_1(sK4)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_385]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_8,plain,
% 2.77/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.77/1.02      | ~ v1_funct_1(X1)
% 2.77/1.02      | ~ v1_relat_1(X1)
% 2.77/1.02      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_22,negated_conjecture,
% 2.77/1.02      ( v1_funct_1(sK4) ),
% 2.77/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_268,plain,
% 2.77/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.77/1.02      | ~ v1_relat_1(X1)
% 2.77/1.02      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 2.77/1.02      | sK4 != X1 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_269,plain,
% 2.77/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.77/1.02      | ~ v1_relat_1(sK4)
% 2.77/1.02      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_268]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_497,plain,
% 2.77/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.77/1.02      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.77/1.02      inference(resolution,[status(thm)],[c_386,c_269]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1024,plain,
% 2.77/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.77/1.02      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.77/1.02      | ~ sP3_iProver_split ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.77/1.02                [c_497]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1308,plain,
% 2.77/1.02      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.77/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.77/1.02      | sP3_iProver_split != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1025,plain,
% 2.77/1.02      ( sP3_iProver_split | sP0_iProver_split ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[])],
% 2.77/1.02                [c_497]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1065,plain,
% 2.77/1.02      ( sP3_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1025]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1066,plain,
% 2.77/1.02      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.77/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.77/1.02      | sP3_iProver_split != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1027,plain,( X0 = X0 ),theory(equality) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1439,plain,
% 2.77/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1027]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_6,plain,
% 2.77/1.02      ( ~ v1_relat_1(X0)
% 2.77/1.02      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.77/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_523,plain,
% 2.77/1.02      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.77/1.02      | sK4 != X0 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_386]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_524,plain,
% 2.77/1.02      ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_523]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1019,plain,
% 2.77/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.77/1.02      | ~ sP0_iProver_split ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.77/1.02                [c_524]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1440,plain,
% 2.77/1.02      ( ~ sP0_iProver_split
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.77/1.02      inference(instantiation,[status(thm)],[c_1019]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1444,plain,
% 2.77/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.77/1.02      | sP0_iProver_split != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1440]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2616,plain,
% 2.77/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.77/1.02      | k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_1308,c_1065,c_1066,c_1439,c_1444]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2617,plain,
% 2.77/1.02      ( k2_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 2.77/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.77/1.02      inference(renaming,[status(thm)],[c_2616]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2625,plain,
% 2.77/1.02      ( k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k11_relat_1(sK4,sK1) ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1580,c_2617]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_11,plain,
% 2.77/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.77/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.77/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_367,plain,
% 2.77/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.77/1.02      | sK4 != X2 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_368,plain,
% 2.77/1.02      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_367]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1456,plain,
% 2.77/1.02      ( k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.77/1.02      inference(equality_resolution,[status(thm)],[c_368]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_18,negated_conjecture,
% 2.77/1.02      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 2.77/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1310,plain,
% 2.77/1.02      ( r1_tarski(k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1515,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(sK4,sK3),k2_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.77/1.02      inference(demodulation,[status(thm)],[c_1456,c_1310]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_3259,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(sK4,sK3),k11_relat_1(sK4,sK1)) != iProver_top ),
% 2.77/1.02      inference(demodulation,[status(thm)],[c_2625,c_1515]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1020,plain,
% 2.77/1.02      ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.77/1.02      | ~ sP1_iProver_split ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.77/1.02                [c_524]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1302,plain,
% 2.77/1.02      ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0)
% 2.77/1.02      | sP1_iProver_split != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1021,plain,
% 2.77/1.02      ( sP1_iProver_split | sP0_iProver_split ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[])],
% 2.77/1.02                [c_524]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2182,plain,
% 2.77/1.02      ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_1302,c_1021,c_1020,c_1439,c_1440]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2186,plain,
% 2.77/1.02      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK1) ),
% 2.77/1.02      inference(superposition,[status(thm)],[c_1550,c_2182]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_7,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
% 2.77/1.02      | ~ v1_relat_1(X0) ),
% 2.77/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_511,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.77/1.02      | sK4 != X0 ),
% 2.77/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_386]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_512,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4)))
% 2.77/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.77/1.02      inference(unflattening,[status(thm)],[c_511]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1022,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4)))
% 2.77/1.02      | ~ sP2_iProver_split ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.77/1.02                [c_512]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1305,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4))) = iProver_top
% 2.77/1.02      | sP2_iProver_split != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1023,plain,
% 2.77/1.02      ( sP2_iProver_split | sP0_iProver_split ),
% 2.77/1.02      inference(splitting,
% 2.77/1.02                [splitting(split),new_symbols(definition,[])],
% 2.77/1.02                [c_512]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1060,plain,
% 2.77/1.02      ( sP2_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1023]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_1061,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4))) = iProver_top
% 2.77/1.02      | sP2_iProver_split != iProver_top ),
% 2.77/1.02      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_2068,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4))) = iProver_top ),
% 2.77/1.02      inference(global_propositional_subsumption,
% 2.77/1.02                [status(thm)],
% 2.77/1.02                [c_1305,c_1060,c_1061,c_1439,c_1444]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_3104,plain,
% 2.77/1.02      ( r1_tarski(k9_relat_1(sK4,X0),k11_relat_1(sK4,sK1)) = iProver_top ),
% 2.77/1.02      inference(demodulation,[status(thm)],[c_2186,c_2068]) ).
% 2.77/1.02  
% 2.77/1.02  cnf(c_3279,plain,
% 2.77/1.02      ( $false ),
% 2.77/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_3259,c_3104]) ).
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/1.02  
% 2.77/1.02  ------                               Statistics
% 2.77/1.02  
% 2.77/1.02  ------ General
% 2.77/1.02  
% 2.77/1.02  abstr_ref_over_cycles:                  0
% 2.77/1.02  abstr_ref_under_cycles:                 0
% 2.77/1.02  gc_basic_clause_elim:                   0
% 2.77/1.02  forced_gc_time:                         0
% 2.77/1.02  parsing_time:                           0.011
% 2.77/1.02  unif_index_cands_time:                  0.
% 2.77/1.02  unif_index_add_time:                    0.
% 2.77/1.02  orderings_time:                         0.
% 2.77/1.02  out_proof_time:                         0.013
% 2.77/1.02  total_time:                             0.136
% 2.77/1.02  num_of_symbols:                         56
% 2.77/1.02  num_of_terms:                           3634
% 2.77/1.02  
% 2.77/1.02  ------ Preprocessing
% 2.77/1.02  
% 2.77/1.02  num_of_splits:                          6
% 2.77/1.02  num_of_split_atoms:                     4
% 2.77/1.02  num_of_reused_defs:                     2
% 2.77/1.02  num_eq_ax_congr_red:                    18
% 2.77/1.02  num_of_sem_filtered_clauses:            1
% 2.77/1.02  num_of_subtypes:                        0
% 2.77/1.02  monotx_restored_types:                  0
% 2.77/1.02  sat_num_of_epr_types:                   0
% 2.77/1.02  sat_num_of_non_cyclic_types:            0
% 2.77/1.02  sat_guarded_non_collapsed_types:        0
% 2.77/1.02  num_pure_diseq_elim:                    0
% 2.77/1.02  simp_replaced_by:                       0
% 2.77/1.02  res_preprocessed:                       106
% 2.77/1.02  prep_upred:                             0
% 2.77/1.02  prep_unflattend:                        53
% 2.77/1.02  smt_new_axioms:                         0
% 2.77/1.02  pred_elim_cands:                        2
% 2.77/1.02  pred_elim:                              4
% 2.77/1.02  pred_elim_cl:                           7
% 2.77/1.02  pred_elim_cycles:                       11
% 2.77/1.02  merged_defs:                            0
% 2.77/1.02  merged_defs_ncl:                        0
% 2.77/1.02  bin_hyper_res:                          0
% 2.77/1.02  prep_cycles:                            4
% 2.77/1.02  pred_elim_time:                         0.014
% 2.77/1.02  splitting_time:                         0.
% 2.77/1.02  sem_filter_time:                        0.
% 2.77/1.02  monotx_time:                            0.001
% 2.77/1.02  subtype_inf_time:                       0.
% 2.77/1.02  
% 2.77/1.02  ------ Problem properties
% 2.77/1.02  
% 2.77/1.02  clauses:                                22
% 2.77/1.02  conjectures:                            2
% 2.77/1.02  epr:                                    4
% 2.77/1.02  horn:                                   16
% 2.77/1.02  ground:                                 8
% 2.77/1.02  unary:                                  5
% 2.77/1.02  binary:                                 10
% 2.77/1.02  lits:                                   48
% 2.77/1.02  lits_eq:                                27
% 2.77/1.02  fd_pure:                                0
% 2.77/1.02  fd_pseudo:                              0
% 2.77/1.02  fd_cond:                                0
% 2.77/1.02  fd_pseudo_cond:                         3
% 2.77/1.02  ac_symbols:                             0
% 2.77/1.02  
% 2.77/1.02  ------ Propositional Solver
% 2.77/1.02  
% 2.77/1.02  prop_solver_calls:                      27
% 2.77/1.02  prop_fast_solver_calls:                 735
% 2.77/1.02  smt_solver_calls:                       0
% 2.77/1.02  smt_fast_solver_calls:                  0
% 2.77/1.02  prop_num_of_clauses:                    1094
% 2.77/1.02  prop_preprocess_simplified:             4362
% 2.77/1.02  prop_fo_subsumed:                       11
% 2.77/1.02  prop_solver_time:                       0.
% 2.77/1.02  smt_solver_time:                        0.
% 2.77/1.02  smt_fast_solver_time:                   0.
% 2.77/1.02  prop_fast_solver_time:                  0.
% 2.77/1.02  prop_unsat_core_time:                   0.
% 2.77/1.02  
% 2.77/1.02  ------ QBF
% 2.77/1.02  
% 2.77/1.02  qbf_q_res:                              0
% 2.77/1.02  qbf_num_tautologies:                    0
% 2.77/1.02  qbf_prep_cycles:                        0
% 2.77/1.02  
% 2.77/1.02  ------ BMC1
% 2.77/1.02  
% 2.77/1.02  bmc1_current_bound:                     -1
% 2.77/1.02  bmc1_last_solved_bound:                 -1
% 2.77/1.02  bmc1_unsat_core_size:                   -1
% 2.77/1.02  bmc1_unsat_core_parents_size:           -1
% 2.77/1.02  bmc1_merge_next_fun:                    0
% 2.77/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.77/1.02  
% 2.77/1.02  ------ Instantiation
% 2.77/1.02  
% 2.77/1.02  inst_num_of_clauses:                    339
% 2.77/1.02  inst_num_in_passive:                    163
% 2.77/1.02  inst_num_in_active:                     143
% 2.77/1.02  inst_num_in_unprocessed:                33
% 2.77/1.02  inst_num_of_loops:                      170
% 2.77/1.02  inst_num_of_learning_restarts:          0
% 2.77/1.02  inst_num_moves_active_passive:          25
% 2.77/1.02  inst_lit_activity:                      0
% 2.77/1.02  inst_lit_activity_moves:                0
% 2.77/1.02  inst_num_tautologies:                   0
% 2.77/1.02  inst_num_prop_implied:                  0
% 2.77/1.02  inst_num_existing_simplified:           0
% 2.77/1.02  inst_num_eq_res_simplified:             0
% 2.77/1.02  inst_num_child_elim:                    0
% 2.77/1.02  inst_num_of_dismatching_blockings:      152
% 2.77/1.02  inst_num_of_non_proper_insts:           380
% 2.77/1.02  inst_num_of_duplicates:                 0
% 2.77/1.02  inst_inst_num_from_inst_to_res:         0
% 2.77/1.02  inst_dismatching_checking_time:         0.
% 2.77/1.02  
% 2.77/1.02  ------ Resolution
% 2.77/1.02  
% 2.77/1.02  res_num_of_clauses:                     0
% 2.77/1.02  res_num_in_passive:                     0
% 2.77/1.02  res_num_in_active:                      0
% 2.77/1.02  res_num_of_loops:                       110
% 2.77/1.02  res_forward_subset_subsumed:            67
% 2.77/1.02  res_backward_subset_subsumed:           0
% 2.77/1.02  res_forward_subsumed:                   0
% 2.77/1.02  res_backward_subsumed:                  0
% 2.77/1.02  res_forward_subsumption_resolution:     0
% 2.77/1.02  res_backward_subsumption_resolution:    0
% 2.77/1.02  res_clause_to_clause_subsumption:       74
% 2.77/1.02  res_orphan_elimination:                 0
% 2.77/1.02  res_tautology_del:                      23
% 2.77/1.02  res_num_eq_res_simplified:              1
% 2.77/1.02  res_num_sel_changes:                    0
% 2.77/1.02  res_moves_from_active_to_pass:          0
% 2.77/1.02  
% 2.77/1.02  ------ Superposition
% 2.77/1.02  
% 2.77/1.02  sup_time_total:                         0.
% 2.77/1.02  sup_time_generating:                    0.
% 2.77/1.02  sup_time_sim_full:                      0.
% 2.77/1.02  sup_time_sim_immed:                     0.
% 2.77/1.02  
% 2.77/1.02  sup_num_of_clauses:                     34
% 2.77/1.02  sup_num_in_active:                      25
% 2.77/1.02  sup_num_in_passive:                     9
% 2.77/1.02  sup_num_of_loops:                       33
% 2.77/1.02  sup_fw_superposition:                   12
% 2.77/1.02  sup_bw_superposition:                   6
% 2.77/1.02  sup_immediate_simplified:               1
% 2.77/1.02  sup_given_eliminated:                   0
% 2.77/1.02  comparisons_done:                       0
% 2.77/1.02  comparisons_avoided:                    4
% 2.77/1.02  
% 2.77/1.02  ------ Simplifications
% 2.77/1.02  
% 2.77/1.02  
% 2.77/1.02  sim_fw_subset_subsumed:                 0
% 2.77/1.02  sim_bw_subset_subsumed:                 0
% 2.77/1.02  sim_fw_subsumed:                        0
% 2.77/1.02  sim_bw_subsumed:                        0
% 2.77/1.02  sim_fw_subsumption_res:                 1
% 2.77/1.02  sim_bw_subsumption_res:                 0
% 2.77/1.02  sim_tautology_del:                      0
% 2.77/1.02  sim_eq_tautology_del:                   2
% 2.77/1.02  sim_eq_res_simp:                        0
% 2.77/1.02  sim_fw_demodulated:                     0
% 2.77/1.02  sim_bw_demodulated:                     9
% 2.77/1.02  sim_light_normalised:                   1
% 2.77/1.02  sim_joinable_taut:                      0
% 2.77/1.02  sim_joinable_simp:                      0
% 2.77/1.02  sim_ac_normalised:                      0
% 2.77/1.02  sim_smt_subsumption:                    0
% 2.77/1.02  
%------------------------------------------------------------------------------
