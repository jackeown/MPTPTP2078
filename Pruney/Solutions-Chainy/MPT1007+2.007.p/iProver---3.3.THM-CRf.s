%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:43 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  205 (1189 expanded)
%              Number of clauses        :  120 ( 352 expanded)
%              Number of leaves         :   26 ( 269 expanded)
%              Depth                    :   25
%              Number of atoms          :  545 (3362 expanded)
%              Number of equality atoms :  221 (1094 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f50])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f88])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f85,f89])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f89])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f84,f89])).

fof(f86,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f90,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f14,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_444,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_445,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_2084,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_1655,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2276,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_2278,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_2279,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2278])).

cnf(c_2319,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2084,c_2276,c_2279])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2095,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3537,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2319,c_2095])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_26,c_9])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_26,c_24,c_9])).

cnf(c_435,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_30])).

cnf(c_436,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_2292,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_436])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2094,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3102,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2319,c_2094])).

cnf(c_3224,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2292,c_3102])).

cnf(c_3768,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3537,c_3224])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2093,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_22,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X4))
    | r2_hidden(k1_funct_1(X4,X3),X5)
    | ~ v1_funct_1(X4)
    | ~ v1_relat_1(X4)
    | X0 != X4
    | X2 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_24])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_414,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X3,X2))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_370,c_30])).

cnf(c_415,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ v1_funct_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_419,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),X1)
    | ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_32])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_2085,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_2535,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2085])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2088,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2567,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2535,c_2088])).

cnf(c_3614,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2093,c_2567])).

cnf(c_3880,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_2276,c_2279])).

cnf(c_3884,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3768,c_3880])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2091,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3225,plain,
    ( k7_relat_1(sK3,X0) = k1_xboole_0
    | k9_relat_1(sK3,X0) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_2091])).

cnf(c_3292,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3224,c_3225])).

cnf(c_3293,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3292,c_2292])).

cnf(c_3294,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3293,c_2292])).

cnf(c_3295,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3294])).

cnf(c_3297,plain,
    ( sK3 = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3294,c_2276,c_2278,c_3295])).

cnf(c_3298,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3297])).

cnf(c_3886,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3884,c_3298])).

cnf(c_3890,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3886])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2099,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_394,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2)
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_398,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_32,c_30,c_29])).

cnf(c_2086,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_2720,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2099,c_2086])).

cnf(c_2287,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0))
    | v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2629,plain,
    ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
    | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_2287])).

cnf(c_2631,plain,
    ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
    | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2629])).

cnf(c_2630,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
    | ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_2633,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2630])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2651,plain,
    ( ~ v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2652,plain,
    ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_2930,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2720,c_2631,c_2633,c_2652])).

cnf(c_4029,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3890,c_2930])).

cnf(c_14,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_16,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_20,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_602,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_603,plain,
    ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ v1_relat_1(k6_relat_1(X1))
    | k1_funct_1(k6_relat_1(X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_21,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_613,plain,
    ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
    | k1_funct_1(k6_relat_1(X1),X0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_603,c_21])).

cnf(c_2079,plain,
    ( k1_funct_1(k6_relat_1(X0),X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_2644,plain,
    ( k1_funct_1(k6_relat_1(k1_xboole_0),X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_2079])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2645,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2644,c_11,c_14])).

cnf(c_56,plain,
    ( v1_relat_1(k6_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_544,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2)
    | X1 != X2
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_16])).

cnf(c_545,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_516,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_517,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_529,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_517,c_1])).

cnf(c_549,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_545,c_529])).

cnf(c_550,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0)
    | k1_funct_1(X0,X1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_549])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_737,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(X0,X1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_550,c_2])).

cnf(c_738,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_1684,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_1661,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2302,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k6_relat_1(X1))
    | X0 != k6_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_2307,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_xboole_0))
    | v1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2302])).

cnf(c_1656,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2446,plain,
    ( X0 != X1
    | X0 = k6_relat_1(X2)
    | k6_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1656])).

cnf(c_2447,plain,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_2723,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_56,c_14,c_738,c_1684,c_2307,c_2447])).

cnf(c_4078,plain,
    ( r2_hidden(k1_xboole_0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4029,c_2723])).

cnf(c_652,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_653,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_2076,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_654,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_2388,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | k1_funct_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2076,c_654,c_2276,c_2279])).

cnf(c_2389,plain,
    ( k1_funct_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2388])).

cnf(c_2571,plain,
    ( k1_funct_1(sK3,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2389,c_2567])).

cnf(c_2583,plain,
    ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2571,c_2088])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4078,c_2583])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.33/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/1.00  
% 2.33/1.00  ------  iProver source info
% 2.33/1.00  
% 2.33/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.33/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/1.00  git: non_committed_changes: false
% 2.33/1.00  git: last_make_outside_of_git: false
% 2.33/1.00  
% 2.33/1.00  ------ 
% 2.33/1.00  
% 2.33/1.00  ------ Input Options
% 2.33/1.00  
% 2.33/1.00  --out_options                           all
% 2.33/1.00  --tptp_safe_out                         true
% 2.33/1.00  --problem_path                          ""
% 2.33/1.00  --include_path                          ""
% 2.33/1.00  --clausifier                            res/vclausify_rel
% 2.33/1.00  --clausifier_options                    --mode clausify
% 2.33/1.00  --stdin                                 false
% 2.33/1.00  --stats_out                             all
% 2.33/1.00  
% 2.33/1.00  ------ General Options
% 2.33/1.00  
% 2.33/1.00  --fof                                   false
% 2.33/1.00  --time_out_real                         305.
% 2.33/1.00  --time_out_virtual                      -1.
% 2.33/1.00  --symbol_type_check                     false
% 2.33/1.00  --clausify_out                          false
% 2.33/1.00  --sig_cnt_out                           false
% 2.33/1.00  --trig_cnt_out                          false
% 2.33/1.00  --trig_cnt_out_tolerance                1.
% 2.33/1.00  --trig_cnt_out_sk_spl                   false
% 2.33/1.00  --abstr_cl_out                          false
% 2.33/1.00  
% 2.33/1.00  ------ Global Options
% 2.33/1.00  
% 2.33/1.00  --schedule                              default
% 2.33/1.00  --add_important_lit                     false
% 2.33/1.00  --prop_solver_per_cl                    1000
% 2.33/1.00  --min_unsat_core                        false
% 2.33/1.00  --soft_assumptions                      false
% 2.33/1.00  --soft_lemma_size                       3
% 2.33/1.00  --prop_impl_unit_size                   0
% 2.33/1.00  --prop_impl_unit                        []
% 2.33/1.00  --share_sel_clauses                     true
% 2.33/1.00  --reset_solvers                         false
% 2.33/1.00  --bc_imp_inh                            [conj_cone]
% 2.33/1.00  --conj_cone_tolerance                   3.
% 2.33/1.00  --extra_neg_conj                        none
% 2.33/1.00  --large_theory_mode                     true
% 2.33/1.00  --prolific_symb_bound                   200
% 2.33/1.00  --lt_threshold                          2000
% 2.33/1.00  --clause_weak_htbl                      true
% 2.33/1.00  --gc_record_bc_elim                     false
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing Options
% 2.33/1.00  
% 2.33/1.00  --preprocessing_flag                    true
% 2.33/1.00  --time_out_prep_mult                    0.1
% 2.33/1.00  --splitting_mode                        input
% 2.33/1.00  --splitting_grd                         true
% 2.33/1.00  --splitting_cvd                         false
% 2.33/1.00  --splitting_cvd_svl                     false
% 2.33/1.00  --splitting_nvd                         32
% 2.33/1.00  --sub_typing                            true
% 2.33/1.00  --prep_gs_sim                           true
% 2.33/1.00  --prep_unflatten                        true
% 2.33/1.00  --prep_res_sim                          true
% 2.33/1.00  --prep_upred                            true
% 2.33/1.00  --prep_sem_filter                       exhaustive
% 2.33/1.00  --prep_sem_filter_out                   false
% 2.33/1.00  --pred_elim                             true
% 2.33/1.00  --res_sim_input                         true
% 2.33/1.00  --eq_ax_congr_red                       true
% 2.33/1.00  --pure_diseq_elim                       true
% 2.33/1.00  --brand_transform                       false
% 2.33/1.00  --non_eq_to_eq                          false
% 2.33/1.00  --prep_def_merge                        true
% 2.33/1.00  --prep_def_merge_prop_impl              false
% 2.33/1.00  --prep_def_merge_mbd                    true
% 2.33/1.00  --prep_def_merge_tr_red                 false
% 2.33/1.00  --prep_def_merge_tr_cl                  false
% 2.33/1.00  --smt_preprocessing                     true
% 2.33/1.00  --smt_ac_axioms                         fast
% 2.33/1.00  --preprocessed_out                      false
% 2.33/1.00  --preprocessed_stats                    false
% 2.33/1.00  
% 2.33/1.00  ------ Abstraction refinement Options
% 2.33/1.00  
% 2.33/1.00  --abstr_ref                             []
% 2.33/1.00  --abstr_ref_prep                        false
% 2.33/1.00  --abstr_ref_until_sat                   false
% 2.33/1.00  --abstr_ref_sig_restrict                funpre
% 2.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.00  --abstr_ref_under                       []
% 2.33/1.00  
% 2.33/1.00  ------ SAT Options
% 2.33/1.00  
% 2.33/1.00  --sat_mode                              false
% 2.33/1.00  --sat_fm_restart_options                ""
% 2.33/1.00  --sat_gr_def                            false
% 2.33/1.00  --sat_epr_types                         true
% 2.33/1.00  --sat_non_cyclic_types                  false
% 2.33/1.00  --sat_finite_models                     false
% 2.33/1.00  --sat_fm_lemmas                         false
% 2.33/1.00  --sat_fm_prep                           false
% 2.33/1.00  --sat_fm_uc_incr                        true
% 2.33/1.00  --sat_out_model                         small
% 2.33/1.00  --sat_out_clauses                       false
% 2.33/1.00  
% 2.33/1.00  ------ QBF Options
% 2.33/1.00  
% 2.33/1.00  --qbf_mode                              false
% 2.33/1.00  --qbf_elim_univ                         false
% 2.33/1.00  --qbf_dom_inst                          none
% 2.33/1.00  --qbf_dom_pre_inst                      false
% 2.33/1.00  --qbf_sk_in                             false
% 2.33/1.00  --qbf_pred_elim                         true
% 2.33/1.00  --qbf_split                             512
% 2.33/1.00  
% 2.33/1.00  ------ BMC1 Options
% 2.33/1.00  
% 2.33/1.00  --bmc1_incremental                      false
% 2.33/1.00  --bmc1_axioms                           reachable_all
% 2.33/1.00  --bmc1_min_bound                        0
% 2.33/1.00  --bmc1_max_bound                        -1
% 2.33/1.00  --bmc1_max_bound_default                -1
% 2.33/1.00  --bmc1_symbol_reachability              true
% 2.33/1.00  --bmc1_property_lemmas                  false
% 2.33/1.00  --bmc1_k_induction                      false
% 2.33/1.00  --bmc1_non_equiv_states                 false
% 2.33/1.00  --bmc1_deadlock                         false
% 2.33/1.00  --bmc1_ucm                              false
% 2.33/1.00  --bmc1_add_unsat_core                   none
% 2.33/1.00  --bmc1_unsat_core_children              false
% 2.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.00  --bmc1_out_stat                         full
% 2.33/1.00  --bmc1_ground_init                      false
% 2.33/1.00  --bmc1_pre_inst_next_state              false
% 2.33/1.00  --bmc1_pre_inst_state                   false
% 2.33/1.00  --bmc1_pre_inst_reach_state             false
% 2.33/1.00  --bmc1_out_unsat_core                   false
% 2.33/1.00  --bmc1_aig_witness_out                  false
% 2.33/1.00  --bmc1_verbose                          false
% 2.33/1.00  --bmc1_dump_clauses_tptp                false
% 2.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.00  --bmc1_dump_file                        -
% 2.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.00  --bmc1_ucm_extend_mode                  1
% 2.33/1.00  --bmc1_ucm_init_mode                    2
% 2.33/1.00  --bmc1_ucm_cone_mode                    none
% 2.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.00  --bmc1_ucm_relax_model                  4
% 2.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.00  --bmc1_ucm_layered_model                none
% 2.33/1.00  --bmc1_ucm_max_lemma_size               10
% 2.33/1.00  
% 2.33/1.00  ------ AIG Options
% 2.33/1.00  
% 2.33/1.00  --aig_mode                              false
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation Options
% 2.33/1.00  
% 2.33/1.00  --instantiation_flag                    true
% 2.33/1.00  --inst_sos_flag                         false
% 2.33/1.00  --inst_sos_phase                        true
% 2.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel_side                     num_symb
% 2.33/1.00  --inst_solver_per_active                1400
% 2.33/1.00  --inst_solver_calls_frac                1.
% 2.33/1.00  --inst_passive_queue_type               priority_queues
% 2.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.00  --inst_passive_queues_freq              [25;2]
% 2.33/1.00  --inst_dismatching                      true
% 2.33/1.00  --inst_eager_unprocessed_to_passive     true
% 2.33/1.00  --inst_prop_sim_given                   true
% 2.33/1.00  --inst_prop_sim_new                     false
% 2.33/1.00  --inst_subs_new                         false
% 2.33/1.00  --inst_eq_res_simp                      false
% 2.33/1.00  --inst_subs_given                       false
% 2.33/1.00  --inst_orphan_elimination               true
% 2.33/1.00  --inst_learning_loop_flag               true
% 2.33/1.00  --inst_learning_start                   3000
% 2.33/1.00  --inst_learning_factor                  2
% 2.33/1.00  --inst_start_prop_sim_after_learn       3
% 2.33/1.00  --inst_sel_renew                        solver
% 2.33/1.00  --inst_lit_activity_flag                true
% 2.33/1.00  --inst_restr_to_given                   false
% 2.33/1.00  --inst_activity_threshold               500
% 2.33/1.00  --inst_out_proof                        true
% 2.33/1.00  
% 2.33/1.00  ------ Resolution Options
% 2.33/1.00  
% 2.33/1.00  --resolution_flag                       true
% 2.33/1.00  --res_lit_sel                           adaptive
% 2.33/1.00  --res_lit_sel_side                      none
% 2.33/1.00  --res_ordering                          kbo
% 2.33/1.00  --res_to_prop_solver                    active
% 2.33/1.00  --res_prop_simpl_new                    false
% 2.33/1.00  --res_prop_simpl_given                  true
% 2.33/1.00  --res_passive_queue_type                priority_queues
% 2.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.00  --res_passive_queues_freq               [15;5]
% 2.33/1.00  --res_forward_subs                      full
% 2.33/1.00  --res_backward_subs                     full
% 2.33/1.00  --res_forward_subs_resolution           true
% 2.33/1.00  --res_backward_subs_resolution          true
% 2.33/1.00  --res_orphan_elimination                true
% 2.33/1.00  --res_time_limit                        2.
% 2.33/1.00  --res_out_proof                         true
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Options
% 2.33/1.00  
% 2.33/1.00  --superposition_flag                    true
% 2.33/1.00  --sup_passive_queue_type                priority_queues
% 2.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.00  --demod_completeness_check              fast
% 2.33/1.00  --demod_use_ground                      true
% 2.33/1.00  --sup_to_prop_solver                    passive
% 2.33/1.00  --sup_prop_simpl_new                    true
% 2.33/1.00  --sup_prop_simpl_given                  true
% 2.33/1.00  --sup_fun_splitting                     false
% 2.33/1.00  --sup_smt_interval                      50000
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Simplification Setup
% 2.33/1.00  
% 2.33/1.00  --sup_indices_passive                   []
% 2.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_full_bw                           [BwDemod]
% 2.33/1.00  --sup_immed_triv                        [TrivRules]
% 2.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_immed_bw_main                     []
% 2.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  
% 2.33/1.00  ------ Combination Options
% 2.33/1.00  
% 2.33/1.00  --comb_res_mult                         3
% 2.33/1.00  --comb_sup_mult                         2
% 2.33/1.00  --comb_inst_mult                        10
% 2.33/1.00  
% 2.33/1.00  ------ Debug Options
% 2.33/1.00  
% 2.33/1.00  --dbg_backtrace                         false
% 2.33/1.00  --dbg_dump_prop_clauses                 false
% 2.33/1.00  --dbg_dump_prop_clauses_file            -
% 2.33/1.00  --dbg_out_stat                          false
% 2.33/1.00  ------ Parsing...
% 2.33/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/1.00  ------ Proving...
% 2.33/1.00  ------ Problem Properties 
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  clauses                                 29
% 2.33/1.00  conjectures                             2
% 2.33/1.00  EPR                                     4
% 2.33/1.00  Horn                                    25
% 2.33/1.00  unary                                   9
% 2.33/1.00  binary                                  9
% 2.33/1.00  lits                                    61
% 2.33/1.00  lits eq                                 21
% 2.33/1.00  fd_pure                                 0
% 2.33/1.00  fd_pseudo                               0
% 2.33/1.00  fd_cond                                 2
% 2.33/1.00  fd_pseudo_cond                          2
% 2.33/1.00  AC symbols                              0
% 2.33/1.00  
% 2.33/1.00  ------ Schedule dynamic 5 is on 
% 2.33/1.00  
% 2.33/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  ------ 
% 2.33/1.00  Current options:
% 2.33/1.00  ------ 
% 2.33/1.00  
% 2.33/1.00  ------ Input Options
% 2.33/1.00  
% 2.33/1.00  --out_options                           all
% 2.33/1.00  --tptp_safe_out                         true
% 2.33/1.00  --problem_path                          ""
% 2.33/1.00  --include_path                          ""
% 2.33/1.00  --clausifier                            res/vclausify_rel
% 2.33/1.00  --clausifier_options                    --mode clausify
% 2.33/1.00  --stdin                                 false
% 2.33/1.00  --stats_out                             all
% 2.33/1.00  
% 2.33/1.00  ------ General Options
% 2.33/1.00  
% 2.33/1.00  --fof                                   false
% 2.33/1.00  --time_out_real                         305.
% 2.33/1.00  --time_out_virtual                      -1.
% 2.33/1.00  --symbol_type_check                     false
% 2.33/1.00  --clausify_out                          false
% 2.33/1.00  --sig_cnt_out                           false
% 2.33/1.00  --trig_cnt_out                          false
% 2.33/1.00  --trig_cnt_out_tolerance                1.
% 2.33/1.00  --trig_cnt_out_sk_spl                   false
% 2.33/1.00  --abstr_cl_out                          false
% 2.33/1.00  
% 2.33/1.00  ------ Global Options
% 2.33/1.00  
% 2.33/1.00  --schedule                              default
% 2.33/1.00  --add_important_lit                     false
% 2.33/1.00  --prop_solver_per_cl                    1000
% 2.33/1.00  --min_unsat_core                        false
% 2.33/1.00  --soft_assumptions                      false
% 2.33/1.00  --soft_lemma_size                       3
% 2.33/1.00  --prop_impl_unit_size                   0
% 2.33/1.00  --prop_impl_unit                        []
% 2.33/1.00  --share_sel_clauses                     true
% 2.33/1.00  --reset_solvers                         false
% 2.33/1.00  --bc_imp_inh                            [conj_cone]
% 2.33/1.00  --conj_cone_tolerance                   3.
% 2.33/1.00  --extra_neg_conj                        none
% 2.33/1.00  --large_theory_mode                     true
% 2.33/1.00  --prolific_symb_bound                   200
% 2.33/1.00  --lt_threshold                          2000
% 2.33/1.00  --clause_weak_htbl                      true
% 2.33/1.00  --gc_record_bc_elim                     false
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing Options
% 2.33/1.00  
% 2.33/1.00  --preprocessing_flag                    true
% 2.33/1.00  --time_out_prep_mult                    0.1
% 2.33/1.00  --splitting_mode                        input
% 2.33/1.00  --splitting_grd                         true
% 2.33/1.00  --splitting_cvd                         false
% 2.33/1.00  --splitting_cvd_svl                     false
% 2.33/1.00  --splitting_nvd                         32
% 2.33/1.00  --sub_typing                            true
% 2.33/1.00  --prep_gs_sim                           true
% 2.33/1.00  --prep_unflatten                        true
% 2.33/1.00  --prep_res_sim                          true
% 2.33/1.00  --prep_upred                            true
% 2.33/1.00  --prep_sem_filter                       exhaustive
% 2.33/1.00  --prep_sem_filter_out                   false
% 2.33/1.00  --pred_elim                             true
% 2.33/1.00  --res_sim_input                         true
% 2.33/1.00  --eq_ax_congr_red                       true
% 2.33/1.00  --pure_diseq_elim                       true
% 2.33/1.00  --brand_transform                       false
% 2.33/1.00  --non_eq_to_eq                          false
% 2.33/1.00  --prep_def_merge                        true
% 2.33/1.00  --prep_def_merge_prop_impl              false
% 2.33/1.00  --prep_def_merge_mbd                    true
% 2.33/1.00  --prep_def_merge_tr_red                 false
% 2.33/1.00  --prep_def_merge_tr_cl                  false
% 2.33/1.00  --smt_preprocessing                     true
% 2.33/1.00  --smt_ac_axioms                         fast
% 2.33/1.00  --preprocessed_out                      false
% 2.33/1.00  --preprocessed_stats                    false
% 2.33/1.00  
% 2.33/1.00  ------ Abstraction refinement Options
% 2.33/1.00  
% 2.33/1.00  --abstr_ref                             []
% 2.33/1.00  --abstr_ref_prep                        false
% 2.33/1.00  --abstr_ref_until_sat                   false
% 2.33/1.00  --abstr_ref_sig_restrict                funpre
% 2.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.00  --abstr_ref_under                       []
% 2.33/1.00  
% 2.33/1.00  ------ SAT Options
% 2.33/1.00  
% 2.33/1.00  --sat_mode                              false
% 2.33/1.00  --sat_fm_restart_options                ""
% 2.33/1.00  --sat_gr_def                            false
% 2.33/1.00  --sat_epr_types                         true
% 2.33/1.00  --sat_non_cyclic_types                  false
% 2.33/1.00  --sat_finite_models                     false
% 2.33/1.00  --sat_fm_lemmas                         false
% 2.33/1.00  --sat_fm_prep                           false
% 2.33/1.00  --sat_fm_uc_incr                        true
% 2.33/1.00  --sat_out_model                         small
% 2.33/1.00  --sat_out_clauses                       false
% 2.33/1.00  
% 2.33/1.00  ------ QBF Options
% 2.33/1.00  
% 2.33/1.00  --qbf_mode                              false
% 2.33/1.00  --qbf_elim_univ                         false
% 2.33/1.00  --qbf_dom_inst                          none
% 2.33/1.00  --qbf_dom_pre_inst                      false
% 2.33/1.00  --qbf_sk_in                             false
% 2.33/1.00  --qbf_pred_elim                         true
% 2.33/1.00  --qbf_split                             512
% 2.33/1.00  
% 2.33/1.00  ------ BMC1 Options
% 2.33/1.00  
% 2.33/1.00  --bmc1_incremental                      false
% 2.33/1.00  --bmc1_axioms                           reachable_all
% 2.33/1.00  --bmc1_min_bound                        0
% 2.33/1.00  --bmc1_max_bound                        -1
% 2.33/1.00  --bmc1_max_bound_default                -1
% 2.33/1.00  --bmc1_symbol_reachability              true
% 2.33/1.00  --bmc1_property_lemmas                  false
% 2.33/1.00  --bmc1_k_induction                      false
% 2.33/1.00  --bmc1_non_equiv_states                 false
% 2.33/1.00  --bmc1_deadlock                         false
% 2.33/1.00  --bmc1_ucm                              false
% 2.33/1.00  --bmc1_add_unsat_core                   none
% 2.33/1.00  --bmc1_unsat_core_children              false
% 2.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.00  --bmc1_out_stat                         full
% 2.33/1.00  --bmc1_ground_init                      false
% 2.33/1.00  --bmc1_pre_inst_next_state              false
% 2.33/1.00  --bmc1_pre_inst_state                   false
% 2.33/1.00  --bmc1_pre_inst_reach_state             false
% 2.33/1.00  --bmc1_out_unsat_core                   false
% 2.33/1.00  --bmc1_aig_witness_out                  false
% 2.33/1.00  --bmc1_verbose                          false
% 2.33/1.00  --bmc1_dump_clauses_tptp                false
% 2.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.00  --bmc1_dump_file                        -
% 2.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.00  --bmc1_ucm_extend_mode                  1
% 2.33/1.00  --bmc1_ucm_init_mode                    2
% 2.33/1.00  --bmc1_ucm_cone_mode                    none
% 2.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.00  --bmc1_ucm_relax_model                  4
% 2.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.00  --bmc1_ucm_layered_model                none
% 2.33/1.00  --bmc1_ucm_max_lemma_size               10
% 2.33/1.00  
% 2.33/1.00  ------ AIG Options
% 2.33/1.00  
% 2.33/1.00  --aig_mode                              false
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation Options
% 2.33/1.00  
% 2.33/1.00  --instantiation_flag                    true
% 2.33/1.00  --inst_sos_flag                         false
% 2.33/1.00  --inst_sos_phase                        true
% 2.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel_side                     none
% 2.33/1.00  --inst_solver_per_active                1400
% 2.33/1.00  --inst_solver_calls_frac                1.
% 2.33/1.00  --inst_passive_queue_type               priority_queues
% 2.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.00  --inst_passive_queues_freq              [25;2]
% 2.33/1.00  --inst_dismatching                      true
% 2.33/1.00  --inst_eager_unprocessed_to_passive     true
% 2.33/1.00  --inst_prop_sim_given                   true
% 2.33/1.00  --inst_prop_sim_new                     false
% 2.33/1.00  --inst_subs_new                         false
% 2.33/1.00  --inst_eq_res_simp                      false
% 2.33/1.00  --inst_subs_given                       false
% 2.33/1.00  --inst_orphan_elimination               true
% 2.33/1.00  --inst_learning_loop_flag               true
% 2.33/1.00  --inst_learning_start                   3000
% 2.33/1.00  --inst_learning_factor                  2
% 2.33/1.00  --inst_start_prop_sim_after_learn       3
% 2.33/1.00  --inst_sel_renew                        solver
% 2.33/1.00  --inst_lit_activity_flag                true
% 2.33/1.00  --inst_restr_to_given                   false
% 2.33/1.00  --inst_activity_threshold               500
% 2.33/1.00  --inst_out_proof                        true
% 2.33/1.00  
% 2.33/1.00  ------ Resolution Options
% 2.33/1.00  
% 2.33/1.00  --resolution_flag                       false
% 2.33/1.00  --res_lit_sel                           adaptive
% 2.33/1.00  --res_lit_sel_side                      none
% 2.33/1.00  --res_ordering                          kbo
% 2.33/1.00  --res_to_prop_solver                    active
% 2.33/1.00  --res_prop_simpl_new                    false
% 2.33/1.00  --res_prop_simpl_given                  true
% 2.33/1.00  --res_passive_queue_type                priority_queues
% 2.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.00  --res_passive_queues_freq               [15;5]
% 2.33/1.00  --res_forward_subs                      full
% 2.33/1.00  --res_backward_subs                     full
% 2.33/1.00  --res_forward_subs_resolution           true
% 2.33/1.00  --res_backward_subs_resolution          true
% 2.33/1.00  --res_orphan_elimination                true
% 2.33/1.00  --res_time_limit                        2.
% 2.33/1.00  --res_out_proof                         true
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Options
% 2.33/1.00  
% 2.33/1.00  --superposition_flag                    true
% 2.33/1.00  --sup_passive_queue_type                priority_queues
% 2.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.00  --demod_completeness_check              fast
% 2.33/1.00  --demod_use_ground                      true
% 2.33/1.00  --sup_to_prop_solver                    passive
% 2.33/1.00  --sup_prop_simpl_new                    true
% 2.33/1.00  --sup_prop_simpl_given                  true
% 2.33/1.00  --sup_fun_splitting                     false
% 2.33/1.00  --sup_smt_interval                      50000
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Simplification Setup
% 2.33/1.00  
% 2.33/1.00  --sup_indices_passive                   []
% 2.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_full_bw                           [BwDemod]
% 2.33/1.00  --sup_immed_triv                        [TrivRules]
% 2.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_immed_bw_main                     []
% 2.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  
% 2.33/1.00  ------ Combination Options
% 2.33/1.00  
% 2.33/1.00  --comb_res_mult                         3
% 2.33/1.00  --comb_sup_mult                         2
% 2.33/1.00  --comb_inst_mult                        10
% 2.33/1.00  
% 2.33/1.00  ------ Debug Options
% 2.33/1.00  
% 2.33/1.00  --dbg_backtrace                         false
% 2.33/1.00  --dbg_dump_prop_clauses                 false
% 2.33/1.00  --dbg_dump_prop_clauses_file            -
% 2.33/1.00  --dbg_out_stat                          false
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  ------ Proving...
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS status Theorem for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  fof(f20,axiom,(
% 2.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f38,plain,(
% 2.33/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/1.00    inference(ennf_transformation,[],[f20])).
% 2.33/1.00  
% 2.33/1.00  fof(f79,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f38])).
% 2.33/1.00  
% 2.33/1.00  fof(f23,conjecture,(
% 2.33/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f24,negated_conjecture,(
% 2.33/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.33/1.00    inference(negated_conjecture,[],[f23])).
% 2.33/1.00  
% 2.33/1.00  fof(f42,plain,(
% 2.33/1.00    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.33/1.00    inference(ennf_transformation,[],[f24])).
% 2.33/1.00  
% 2.33/1.00  fof(f43,plain,(
% 2.33/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.33/1.00    inference(flattening,[],[f42])).
% 2.33/1.00  
% 2.33/1.00  fof(f50,plain,(
% 2.33/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f51,plain,(
% 2.33/1.00    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f43,f50])).
% 2.33/1.00  
% 2.33/1.00  fof(f85,plain,(
% 2.33/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.33/1.00    inference(cnf_transformation,[],[f51])).
% 2.33/1.00  
% 2.33/1.00  fof(f4,axiom,(
% 2.33/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f56,plain,(
% 2.33/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f4])).
% 2.33/1.00  
% 2.33/1.00  fof(f5,axiom,(
% 2.33/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f57,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f5])).
% 2.33/1.00  
% 2.33/1.00  fof(f6,axiom,(
% 2.33/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f58,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f6])).
% 2.33/1.00  
% 2.33/1.00  fof(f88,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.33/1.00    inference(definition_unfolding,[],[f57,f58])).
% 2.33/1.00  
% 2.33/1.00  fof(f89,plain,(
% 2.33/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.33/1.00    inference(definition_unfolding,[],[f56,f88])).
% 2.33/1.00  
% 2.33/1.00  fof(f92,plain,(
% 2.33/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 2.33/1.00    inference(definition_unfolding,[],[f85,f89])).
% 2.33/1.00  
% 2.33/1.00  fof(f8,axiom,(
% 2.33/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f25,plain,(
% 2.33/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f8])).
% 2.33/1.00  
% 2.33/1.00  fof(f60,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f25])).
% 2.33/1.00  
% 2.33/1.00  fof(f91,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.33/1.00    inference(definition_unfolding,[],[f60,f89])).
% 2.33/1.00  
% 2.33/1.00  fof(f21,axiom,(
% 2.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f39,plain,(
% 2.33/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/1.00    inference(ennf_transformation,[],[f21])).
% 2.33/1.00  
% 2.33/1.00  fof(f80,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f11,axiom,(
% 2.33/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f28,plain,(
% 2.33/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.33/1.00    inference(ennf_transformation,[],[f11])).
% 2.33/1.00  
% 2.33/1.00  fof(f29,plain,(
% 2.33/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(flattening,[],[f28])).
% 2.33/1.00  
% 2.33/1.00  fof(f64,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f29])).
% 2.33/1.00  
% 2.33/1.00  fof(f9,axiom,(
% 2.33/1.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f26,plain,(
% 2.33/1.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(ennf_transformation,[],[f9])).
% 2.33/1.00  
% 2.33/1.00  fof(f61,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f26])).
% 2.33/1.00  
% 2.33/1.00  fof(f10,axiom,(
% 2.33/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f27,plain,(
% 2.33/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(ennf_transformation,[],[f10])).
% 2.33/1.00  
% 2.33/1.00  fof(f48,plain,(
% 2.33/1.00    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(nnf_transformation,[],[f27])).
% 2.33/1.00  
% 2.33/1.00  fof(f63,plain,(
% 2.33/1.00    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f48])).
% 2.33/1.00  
% 2.33/1.00  fof(f18,axiom,(
% 2.33/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f35,plain,(
% 2.33/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.33/1.00    inference(ennf_transformation,[],[f18])).
% 2.33/1.00  
% 2.33/1.00  fof(f36,plain,(
% 2.33/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(flattening,[],[f35])).
% 2.33/1.00  
% 2.33/1.00  fof(f77,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f36])).
% 2.33/1.00  
% 2.33/1.00  fof(f81,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f83,plain,(
% 2.33/1.00    v1_funct_1(sK3)),
% 2.33/1.00    inference(cnf_transformation,[],[f51])).
% 2.33/1.00  
% 2.33/1.00  fof(f87,plain,(
% 2.33/1.00    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f51])).
% 2.33/1.00  
% 2.33/1.00  fof(f13,axiom,(
% 2.33/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f30,plain,(
% 2.33/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f13])).
% 2.33/1.00  
% 2.33/1.00  fof(f31,plain,(
% 2.33/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.33/1.00    inference(flattening,[],[f30])).
% 2.33/1.00  
% 2.33/1.00  fof(f68,plain,(
% 2.33/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f31])).
% 2.33/1.00  
% 2.33/1.00  fof(f1,axiom,(
% 2.33/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f44,plain,(
% 2.33/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.00    inference(nnf_transformation,[],[f1])).
% 2.33/1.00  
% 2.33/1.00  fof(f45,plain,(
% 2.33/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.00    inference(rectify,[],[f44])).
% 2.33/1.00  
% 2.33/1.00  fof(f46,plain,(
% 2.33/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f47,plain,(
% 2.33/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 2.33/1.00  
% 2.33/1.00  fof(f53,plain,(
% 2.33/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f47])).
% 2.33/1.00  
% 2.33/1.00  fof(f22,axiom,(
% 2.33/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f40,plain,(
% 2.33/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.33/1.00    inference(ennf_transformation,[],[f22])).
% 2.33/1.00  
% 2.33/1.00  fof(f41,plain,(
% 2.33/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.33/1.00    inference(flattening,[],[f40])).
% 2.33/1.00  
% 2.33/1.00  fof(f82,plain,(
% 2.33/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f41])).
% 2.33/1.00  
% 2.33/1.00  fof(f84,plain,(
% 2.33/1.00    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.33/1.00    inference(cnf_transformation,[],[f51])).
% 2.33/1.00  
% 2.33/1.00  fof(f93,plain,(
% 2.33/1.00    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 2.33/1.00    inference(definition_unfolding,[],[f84,f89])).
% 2.33/1.00  
% 2.33/1.00  fof(f86,plain,(
% 2.33/1.00    k1_xboole_0 != sK2),
% 2.33/1.00    inference(cnf_transformation,[],[f51])).
% 2.33/1.00  
% 2.33/1.00  fof(f7,axiom,(
% 2.33/1.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f59,plain,(
% 2.33/1.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f7])).
% 2.33/1.00  
% 2.33/1.00  fof(f90,plain,(
% 2.33/1.00    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 2.33/1.00    inference(definition_unfolding,[],[f59,f89])).
% 2.33/1.00  
% 2.33/1.00  fof(f14,axiom,(
% 2.33/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f69,plain,(
% 2.33/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.33/1.00    inference(cnf_transformation,[],[f14])).
% 2.33/1.00  
% 2.33/1.00  fof(f16,axiom,(
% 2.33/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f33,plain,(
% 2.33/1.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/1.00    inference(ennf_transformation,[],[f16])).
% 2.33/1.00  
% 2.33/1.00  fof(f34,plain,(
% 2.33/1.00    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/1.00    inference(flattening,[],[f33])).
% 2.33/1.00  
% 2.33/1.00  fof(f49,plain,(
% 2.33/1.00    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/1.00    inference(nnf_transformation,[],[f34])).
% 2.33/1.00  
% 2.33/1.00  fof(f74,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f49])).
% 2.33/1.00  
% 2.33/1.00  fof(f94,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/1.00    inference(equality_resolution,[],[f74])).
% 2.33/1.00  
% 2.33/1.00  fof(f17,axiom,(
% 2.33/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f76,plain,(
% 2.33/1.00    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f17])).
% 2.33/1.00  
% 2.33/1.00  fof(f75,plain,(
% 2.33/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f17])).
% 2.33/1.00  
% 2.33/1.00  fof(f12,axiom,(
% 2.33/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f65,plain,(
% 2.33/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.33/1.00    inference(cnf_transformation,[],[f12])).
% 2.33/1.00  
% 2.33/1.00  fof(f15,axiom,(
% 2.33/1.00    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f32,plain,(
% 2.33/1.00    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f15])).
% 2.33/1.00  
% 2.33/1.00  fof(f70,plain,(
% 2.33/1.00    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f32])).
% 2.33/1.00  
% 2.33/1.00  fof(f71,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f49])).
% 2.33/1.00  
% 2.33/1.00  fof(f96,plain,(
% 2.33/1.00    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/1.00    inference(equality_resolution,[],[f71])).
% 2.33/1.00  
% 2.33/1.00  fof(f52,plain,(
% 2.33/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f47])).
% 2.33/1.00  
% 2.33/1.00  fof(f2,axiom,(
% 2.33/1.00    v1_xboole_0(k1_xboole_0)),
% 2.33/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f54,plain,(
% 2.33/1.00    v1_xboole_0(k1_xboole_0)),
% 2.33/1.00    inference(cnf_transformation,[],[f2])).
% 2.33/1.00  
% 2.33/1.00  cnf(c_24,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | v1_relat_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_30,negated_conjecture,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 2.33/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_444,plain,
% 2.33/1.00      ( v1_relat_1(X0)
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.33/1.00      | sK3 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_445,plain,
% 2.33/1.00      ( v1_relat_1(sK3)
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_444]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2084,plain,
% 2.33/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.33/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1655,plain,( X0 = X0 ),theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2276,plain,
% 2.33/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_1655]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2278,plain,
% 2.33/1.00      ( v1_relat_1(sK3)
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_445]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2279,plain,
% 2.33/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 2.33/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2278]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2319,plain,
% 2.33/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2084,c_2276,c_2279]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_5,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2095,plain,
% 2.33/1.00      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3537,plain,
% 2.33/1.00      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2319,c_2095]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_26,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | v4_relat_1(X0,X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_9,plain,
% 2.33/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_344,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ v1_relat_1(X0)
% 2.33/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.33/1.00      inference(resolution,[status(thm)],[c_26,c_9]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_348,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_344,c_26,c_24,c_9]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_435,plain,
% 2.33/1.00      ( k7_relat_1(X0,X1) = X0
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.33/1.00      | sK3 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_348,c_30]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_436,plain,
% 2.33/1.00      ( k7_relat_1(sK3,X0) = sK3
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2292,plain,
% 2.33/1.00      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
% 2.33/1.00      inference(equality_resolution,[status(thm)],[c_436]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_6,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2094,plain,
% 2.33/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3102,plain,
% 2.33/1.00      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2319,c_2094]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3224,plain,
% 2.33/1.00      ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2292,c_3102]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3768,plain,
% 2.33/1.00      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_3537,c_3224]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_7,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2093,plain,
% 2.33/1.00      ( k11_relat_1(X0,X1) = k1_xboole_0
% 2.33/1.00      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_22,plain,
% 2.33/1.00      ( ~ v5_relat_1(X0,X1)
% 2.33/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.33/1.00      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v1_relat_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_25,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | v5_relat_1(X0,X2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_364,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ r2_hidden(X3,k1_relat_1(X4))
% 2.33/1.00      | r2_hidden(k1_funct_1(X4,X3),X5)
% 2.33/1.00      | ~ v1_funct_1(X4)
% 2.33/1.00      | ~ v1_relat_1(X4)
% 2.33/1.00      | X0 != X4
% 2.33/1.00      | X2 != X5 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_365,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.33/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v1_relat_1(X0) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_364]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_369,plain,
% 2.33/1.00      ( ~ v1_funct_1(X0)
% 2.33/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.33/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_365,c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_370,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.33/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.33/1.00      | ~ v1_funct_1(X0) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_369]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_414,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | r2_hidden(k1_funct_1(X1,X0),X2)
% 2.33/1.00      | ~ v1_funct_1(X1)
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X3,X2))
% 2.33/1.00      | sK3 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_370,c_30]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_415,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.33/1.00      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.33/1.00      | ~ v1_funct_1(sK3)
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_414]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_32,negated_conjecture,
% 2.33/1.00      ( v1_funct_1(sK3) ),
% 2.33/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_419,plain,
% 2.33/1.00      ( r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.33/1.00      | ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_415,c_32]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_420,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.33/1.00      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 2.33/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_419]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2085,plain,
% 2.33/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.33/1.00      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 2.33/1.00      | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2535,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.33/1.00      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 2.33/1.00      inference(equality_resolution,[status(thm)],[c_2085]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_28,negated_conjecture,
% 2.33/1.00      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2088,plain,
% 2.33/1.00      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2567,plain,
% 2.33/1.00      ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2535,c_2088]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3614,plain,
% 2.33/1.00      ( k11_relat_1(sK3,sK1) = k1_xboole_0
% 2.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2093,c_2567]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3880,plain,
% 2.33/1.00      ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_3614,c_2276,c_2279]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3884,plain,
% 2.33/1.00      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_3768,c_3880]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_12,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | k2_relat_1(X0) != k1_xboole_0
% 2.33/1.00      | k1_xboole_0 = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2091,plain,
% 2.33/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 2.33/1.00      | k1_xboole_0 = X0
% 2.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3225,plain,
% 2.33/1.00      ( k7_relat_1(sK3,X0) = k1_xboole_0
% 2.33/1.00      | k9_relat_1(sK3,X0) != k1_xboole_0
% 2.33/1.00      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_3102,c_2091]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3292,plain,
% 2.33/1.00      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0
% 2.33/1.00      | k2_relat_1(sK3) != k1_xboole_0
% 2.33/1.00      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_3224,c_3225]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3293,plain,
% 2.33/1.00      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0
% 2.33/1.00      | k2_relat_1(sK3) != k1_xboole_0
% 2.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_3292,c_2292]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3294,plain,
% 2.33/1.00      ( k2_relat_1(sK3) != k1_xboole_0
% 2.33/1.00      | sK3 = k1_xboole_0
% 2.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_3293,c_2292]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3295,plain,
% 2.33/1.00      ( ~ v1_relat_1(sK3)
% 2.33/1.00      | k2_relat_1(sK3) != k1_xboole_0
% 2.33/1.00      | sK3 = k1_xboole_0 ),
% 2.33/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3294]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3297,plain,
% 2.33/1.00      ( sK3 = k1_xboole_0 | k2_relat_1(sK3) != k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_3294,c_2276,c_2278,c_3295]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3298,plain,
% 2.33/1.00      ( k2_relat_1(sK3) != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_3297]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3886,plain,
% 2.33/1.00      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_3884,c_3298]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3890,plain,
% 2.33/1.00      ( sK3 = k1_xboole_0 ),
% 2.33/1.00      inference(equality_resolution_simp,[status(thm)],[c_3886]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_0,plain,
% 2.33/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2099,plain,
% 2.33/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.33/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_27,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ r2_hidden(X3,X1)
% 2.33/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | k1_xboole_0 = X2 ),
% 2.33/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_31,negated_conjecture,
% 2.33/1.00      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_393,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ r2_hidden(X3,X1)
% 2.33/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 2.33/1.00      | sK2 != X2
% 2.33/1.00      | sK3 != X0
% 2.33/1.00      | k1_xboole_0 = X2 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_394,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 2.33/1.00      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.33/1.00      | r2_hidden(k1_funct_1(sK3,X0),sK2)
% 2.33/1.00      | ~ v1_funct_1(sK3)
% 2.33/1.00      | k1_xboole_0 = sK2 ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_393]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_29,negated_conjecture,
% 2.33/1.00      ( k1_xboole_0 != sK2 ),
% 2.33/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_398,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.33/1.00      | r2_hidden(k1_funct_1(sK3,X0),sK2) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_394,c_32,c_30,c_29]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2086,plain,
% 2.33/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.33/1.00      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2720,plain,
% 2.33/1.00      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 2.33/1.00      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2099,c_2086]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2287,plain,
% 2.33/1.00      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X0)),k2_enumset1(X0,X0,X0,X0))
% 2.33/1.00      | v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2629,plain,
% 2.33/1.00      ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))
% 2.33/1.00      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2287]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2631,plain,
% 2.33/1.00      ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
% 2.33/1.00      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2629]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2630,plain,
% 2.33/1.00      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2)
% 2.33/1.00      | ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_398]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2633,plain,
% 2.33/1.00      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top
% 2.33/1.00      | r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2630]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4,plain,
% 2.33/1.00      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2651,plain,
% 2.33/1.00      ( ~ v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2652,plain,
% 2.33/1.00      ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2930,plain,
% 2.33/1.00      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2720,c_2631,c_2633,c_2652]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4029,plain,
% 2.33/1.00      ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),sK2) = iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_3890,c_2930]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_14,plain,
% 2.33/1.00      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_16,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | ~ v1_funct_1(X1)
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_20,plain,
% 2.33/1.00      ( v1_funct_1(k6_relat_1(X0)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_602,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | k1_funct_1(X1,X0) = k1_xboole_0
% 2.33/1.00      | k6_relat_1(X2) != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_603,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
% 2.33/1.00      | ~ v1_relat_1(k6_relat_1(X1))
% 2.33/1.00      | k1_funct_1(k6_relat_1(X1),X0) = k1_xboole_0 ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_602]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_21,plain,
% 2.33/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_613,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(k6_relat_1(X1)))
% 2.33/1.00      | k1_funct_1(k6_relat_1(X1),X0) = k1_xboole_0 ),
% 2.33/1.00      inference(forward_subsumption_resolution,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_603,c_21]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2079,plain,
% 2.33/1.00      ( k1_funct_1(k6_relat_1(X0),X1) = k1_xboole_0
% 2.33/1.00      | r2_hidden(X1,k1_relat_1(k6_relat_1(X0))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2644,plain,
% 2.33/1.00      ( k1_funct_1(k6_relat_1(k1_xboole_0),X0) = k1_xboole_0
% 2.33/1.00      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_14,c_2079]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_11,plain,
% 2.33/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2645,plain,
% 2.33/1.00      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
% 2.33/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_2644,c_11,c_14]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_56,plain,
% 2.33/1.00      ( v1_relat_1(k6_relat_1(k1_xboole_0)) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_15,plain,
% 2.33/1.00      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_544,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | ~ v1_xboole_0(X2)
% 2.33/1.00      | X1 != X2
% 2.33/1.00      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_16]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_545,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | ~ v1_xboole_0(X1)
% 2.33/1.00      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_544]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_19,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.33/1.00      | ~ v1_funct_1(X1)
% 2.33/1.00      | ~ v1_relat_1(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_516,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | ~ v1_xboole_0(X2)
% 2.33/1.00      | X1 != X2 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_517,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | ~ v1_xboole_0(X1) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_516]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_529,plain,
% 2.33/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | ~ v1_xboole_0(X1) ),
% 2.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_517,c_1]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_549,plain,
% 2.33/1.00      ( ~ v1_relat_1(X1)
% 2.33/1.00      | ~ v1_xboole_0(X1)
% 2.33/1.00      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_545,c_529]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_550,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | ~ v1_xboole_0(X0)
% 2.33/1.00      | k1_funct_1(X0,X1) = k1_xboole_0 ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_549]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2,plain,
% 2.33/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_737,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | k1_funct_1(X0,X1) = k1_xboole_0
% 2.33/1.00      | k1_xboole_0 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_550,c_2]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_738,plain,
% 2.33/1.00      ( ~ v1_relat_1(k1_xboole_0)
% 2.33/1.00      | k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_737]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1684,plain,
% 2.33/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_1655]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1661,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 2.33/1.00      theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2302,plain,
% 2.33/1.00      ( v1_relat_1(X0)
% 2.33/1.00      | ~ v1_relat_1(k6_relat_1(X1))
% 2.33/1.00      | X0 != k6_relat_1(X1) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_1661]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2307,plain,
% 2.33/1.00      ( ~ v1_relat_1(k6_relat_1(k1_xboole_0))
% 2.33/1.00      | v1_relat_1(k1_xboole_0)
% 2.33/1.00      | k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2302]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1656,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2446,plain,
% 2.33/1.00      ( X0 != X1 | X0 = k6_relat_1(X2) | k6_relat_1(X2) != X1 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_1656]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2447,plain,
% 2.33/1.00      ( k6_relat_1(k1_xboole_0) != k1_xboole_0
% 2.33/1.00      | k1_xboole_0 = k6_relat_1(k1_xboole_0)
% 2.33/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2446]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2723,plain,
% 2.33/1.00      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2645,c_56,c_14,c_738,c_1684,c_2307,c_2447]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_4078,plain,
% 2.33/1.00      ( r2_hidden(k1_xboole_0,sK2) = iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_4029,c_2723]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_652,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 2.33/1.00      | ~ v1_relat_1(X1)
% 2.33/1.00      | k1_funct_1(X1,X0) = k1_xboole_0
% 2.33/1.00      | sK3 != X1 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_653,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(sK3))
% 2.33/1.00      | ~ v1_relat_1(sK3)
% 2.33/1.00      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_652]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2076,plain,
% 2.33/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.33/1.00      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_654,plain,
% 2.33/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.33/1.00      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2388,plain,
% 2.33/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 2.33/1.00      | k1_funct_1(sK3,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2076,c_654,c_2276,c_2279]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2389,plain,
% 2.33/1.00      ( k1_funct_1(sK3,X0) = k1_xboole_0
% 2.33/1.00      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_2388]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2571,plain,
% 2.33/1.00      ( k1_funct_1(sK3,sK1) = k1_xboole_0 ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2389,c_2567]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2583,plain,
% 2.33/1.00      ( r2_hidden(k1_xboole_0,sK2) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_2571,c_2088]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(contradiction,plain,
% 2.33/1.00      ( $false ),
% 2.33/1.00      inference(minisat,[status(thm)],[c_4078,c_2583]) ).
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  ------                               Statistics
% 2.33/1.00  
% 2.33/1.00  ------ General
% 2.33/1.00  
% 2.33/1.00  abstr_ref_over_cycles:                  0
% 2.33/1.00  abstr_ref_under_cycles:                 0
% 2.33/1.00  gc_basic_clause_elim:                   0
% 2.33/1.00  forced_gc_time:                         0
% 2.33/1.00  parsing_time:                           0.012
% 2.33/1.00  unif_index_cands_time:                  0.
% 2.33/1.00  unif_index_add_time:                    0.
% 2.33/1.00  orderings_time:                         0.
% 2.33/1.00  out_proof_time:                         0.022
% 2.33/1.00  total_time:                             0.167
% 2.33/1.00  num_of_symbols:                         56
% 2.33/1.00  num_of_terms:                           2774
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing
% 2.33/1.00  
% 2.33/1.00  num_of_splits:                          0
% 2.33/1.00  num_of_split_atoms:                     0
% 2.33/1.00  num_of_reused_defs:                     0
% 2.33/1.00  num_eq_ax_congr_red:                    24
% 2.33/1.00  num_of_sem_filtered_clauses:            1
% 2.33/1.00  num_of_subtypes:                        0
% 2.33/1.00  monotx_restored_types:                  0
% 2.33/1.00  sat_num_of_epr_types:                   0
% 2.33/1.00  sat_num_of_non_cyclic_types:            0
% 2.33/1.00  sat_guarded_non_collapsed_types:        0
% 2.33/1.00  num_pure_diseq_elim:                    0
% 2.33/1.00  simp_replaced_by:                       0
% 2.33/1.00  res_preprocessed:                       150
% 2.33/1.00  prep_upred:                             0
% 2.33/1.00  prep_unflattend:                        67
% 2.33/1.00  smt_new_axioms:                         0
% 2.33/1.00  pred_elim_cands:                        3
% 2.33/1.00  pred_elim:                              6
% 2.33/1.00  pred_elim_cl:                           3
% 2.33/1.00  pred_elim_cycles:                       11
% 2.33/1.00  merged_defs:                            0
% 2.33/1.00  merged_defs_ncl:                        0
% 2.33/1.00  bin_hyper_res:                          0
% 2.33/1.00  prep_cycles:                            4
% 2.33/1.00  pred_elim_time:                         0.02
% 2.33/1.00  splitting_time:                         0.
% 2.33/1.00  sem_filter_time:                        0.
% 2.33/1.00  monotx_time:                            0.001
% 2.33/1.00  subtype_inf_time:                       0.
% 2.33/1.00  
% 2.33/1.00  ------ Problem properties
% 2.33/1.00  
% 2.33/1.00  clauses:                                29
% 2.33/1.00  conjectures:                            2
% 2.33/1.00  epr:                                    4
% 2.33/1.00  horn:                                   25
% 2.33/1.00  ground:                                 6
% 2.33/1.00  unary:                                  9
% 2.33/1.00  binary:                                 9
% 2.33/1.00  lits:                                   61
% 2.33/1.00  lits_eq:                                21
% 2.33/1.00  fd_pure:                                0
% 2.33/1.00  fd_pseudo:                              0
% 2.33/1.00  fd_cond:                                2
% 2.33/1.00  fd_pseudo_cond:                         2
% 2.33/1.00  ac_symbols:                             0
% 2.33/1.00  
% 2.33/1.00  ------ Propositional Solver
% 2.33/1.00  
% 2.33/1.00  prop_solver_calls:                      29
% 2.33/1.00  prop_fast_solver_calls:                 1013
% 2.33/1.00  smt_solver_calls:                       0
% 2.33/1.00  smt_fast_solver_calls:                  0
% 2.33/1.00  prop_num_of_clauses:                    1038
% 2.33/1.00  prop_preprocess_simplified:             5304
% 2.33/1.00  prop_fo_subsumed:                       23
% 2.33/1.00  prop_solver_time:                       0.
% 2.33/1.00  smt_solver_time:                        0.
% 2.33/1.00  smt_fast_solver_time:                   0.
% 2.33/1.00  prop_fast_solver_time:                  0.
% 2.33/1.00  prop_unsat_core_time:                   0.
% 2.33/1.00  
% 2.33/1.00  ------ QBF
% 2.33/1.00  
% 2.33/1.00  qbf_q_res:                              0
% 2.33/1.00  qbf_num_tautologies:                    0
% 2.33/1.00  qbf_prep_cycles:                        0
% 2.33/1.00  
% 2.33/1.00  ------ BMC1
% 2.33/1.00  
% 2.33/1.00  bmc1_current_bound:                     -1
% 2.33/1.00  bmc1_last_solved_bound:                 -1
% 2.33/1.00  bmc1_unsat_core_size:                   -1
% 2.33/1.00  bmc1_unsat_core_parents_size:           -1
% 2.33/1.00  bmc1_merge_next_fun:                    0
% 2.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation
% 2.33/1.00  
% 2.33/1.00  inst_num_of_clauses:                    296
% 2.33/1.00  inst_num_in_passive:                    31
% 2.33/1.00  inst_num_in_active:                     244
% 2.33/1.00  inst_num_in_unprocessed:                21
% 2.33/1.00  inst_num_of_loops:                      280
% 2.33/1.00  inst_num_of_learning_restarts:          0
% 2.33/1.00  inst_num_moves_active_passive:          31
% 2.33/1.00  inst_lit_activity:                      0
% 2.33/1.00  inst_lit_activity_moves:                0
% 2.33/1.00  inst_num_tautologies:                   0
% 2.33/1.00  inst_num_prop_implied:                  0
% 2.33/1.00  inst_num_existing_simplified:           0
% 2.33/1.00  inst_num_eq_res_simplified:             0
% 2.33/1.00  inst_num_child_elim:                    0
% 2.33/1.00  inst_num_of_dismatching_blockings:      111
% 2.33/1.00  inst_num_of_non_proper_insts:           353
% 2.33/1.00  inst_num_of_duplicates:                 0
% 2.33/1.00  inst_inst_num_from_inst_to_res:         0
% 2.33/1.00  inst_dismatching_checking_time:         0.
% 2.33/1.00  
% 2.33/1.00  ------ Resolution
% 2.33/1.00  
% 2.33/1.00  res_num_of_clauses:                     0
% 2.33/1.00  res_num_in_passive:                     0
% 2.33/1.00  res_num_in_active:                      0
% 2.33/1.00  res_num_of_loops:                       154
% 2.33/1.00  res_forward_subset_subsumed:            56
% 2.33/1.00  res_backward_subset_subsumed:           0
% 2.33/1.00  res_forward_subsumed:                   1
% 2.33/1.00  res_backward_subsumed:                  0
% 2.33/1.00  res_forward_subsumption_resolution:     4
% 2.33/1.00  res_backward_subsumption_resolution:    0
% 2.33/1.00  res_clause_to_clause_subsumption:       119
% 2.33/1.00  res_orphan_elimination:                 0
% 2.33/1.00  res_tautology_del:                      42
% 2.33/1.00  res_num_eq_res_simplified:              0
% 2.33/1.00  res_num_sel_changes:                    0
% 2.33/1.00  res_moves_from_active_to_pass:          0
% 2.33/1.00  
% 2.33/1.00  ------ Superposition
% 2.33/1.00  
% 2.33/1.00  sup_time_total:                         0.
% 2.33/1.00  sup_time_generating:                    0.
% 2.33/1.00  sup_time_sim_full:                      0.
% 2.33/1.00  sup_time_sim_immed:                     0.
% 2.33/1.00  
% 2.33/1.00  sup_num_of_clauses:                     46
% 2.33/1.00  sup_num_in_active:                      28
% 2.33/1.00  sup_num_in_passive:                     18
% 2.33/1.00  sup_num_of_loops:                       54
% 2.33/1.00  sup_fw_superposition:                   33
% 2.33/1.00  sup_bw_superposition:                   20
% 2.33/1.00  sup_immediate_simplified:               27
% 2.33/1.00  sup_given_eliminated:                   0
% 2.33/1.00  comparisons_done:                       0
% 2.33/1.00  comparisons_avoided:                    0
% 2.33/1.00  
% 2.33/1.00  ------ Simplifications
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  sim_fw_subset_subsumed:                 7
% 2.33/1.00  sim_bw_subset_subsumed:                 0
% 2.33/1.00  sim_fw_subsumed:                        11
% 2.33/1.00  sim_bw_subsumed:                        1
% 2.33/1.00  sim_fw_subsumption_res:                 0
% 2.33/1.00  sim_bw_subsumption_res:                 0
% 2.33/1.00  sim_tautology_del:                      2
% 2.33/1.00  sim_eq_tautology_del:                   5
% 2.33/1.00  sim_eq_res_simp:                        1
% 2.33/1.00  sim_fw_demodulated:                     4
% 2.33/1.00  sim_bw_demodulated:                     27
% 2.33/1.00  sim_light_normalised:                   16
% 2.33/1.00  sim_joinable_taut:                      0
% 2.33/1.00  sim_joinable_simp:                      0
% 2.33/1.00  sim_ac_normalised:                      0
% 2.33/1.00  sim_smt_subsumption:                    0
% 2.33/1.00  
%------------------------------------------------------------------------------
