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
% DateTime   : Thu Dec  3 12:04:42 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 660 expanded)
%              Number of clauses        :   76 ( 191 expanded)
%              Number of leaves         :   22 ( 145 expanded)
%              Depth                    :   19
%              Number of atoms          :  388 (2071 expanded)
%              Number of equality atoms :  129 ( 625 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f40])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f42])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f73])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f37])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f73])).

cnf(c_8,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_492,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_xboole_0(X2)
    | X1 != X2
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_493,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_xboole_0(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_9,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_505,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_493,c_9])).

cnf(c_1276,plain,
    ( k1_funct_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_3350,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1276])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_449,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_xboole_0(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_450,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_xboole_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_450,c_9])).

cnf(c_546,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_462])).

cnf(c_547,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_262,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_555,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_547,c_263])).

cnf(c_529,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | k1_funct_1(X1,X0) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_505])).

cnf(c_530,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_557,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_555,c_530])).

cnf(c_3353,plain,
    ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3350,c_557])).

cnf(c_19,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1286,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_23])).

cnf(c_317,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_1280,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_1419,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1280])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1287,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2017,plain,
    ( k1_mcart_1(X0) = sK2
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_1287])).

cnf(c_2077,plain,
    ( k1_mcart_1(sK1(sK4)) = sK2
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1286,c_2017])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1289,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1725,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_mcart_1(X0),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_1289])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_273,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(X2,X0),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | sK3 != X3
    | sK4 != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_274,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_278,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),sK3)
    | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_25,c_23,c_22])).

cnf(c_279,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_1283,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_1770,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK4,k1_mcart_1(X0)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1725,c_1283])).

cnf(c_2099,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(k1_funct_1(sK4,sK2),sK3) = iProver_top
    | r2_hidden(sK1(sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2077,c_1770])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2301,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK4),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2099,c_29])).

cnf(c_2307,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1286,c_2301])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_306,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_307,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_1281,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_1983,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top
    | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_1283])).

cnf(c_1406,plain,
    ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X1)),k2_enumset1(X0,X0,X0,X1))
    | v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_1714,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
    | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_1716,plain,
    ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_1715,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3)
    | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_1718,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1715])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1755,plain,
    ( ~ v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1756,plain,
    ( v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1755])).

cnf(c_2210,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1983,c_1716,c_1718,c_1756])).

cnf(c_2355,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2307,c_2210])).

cnf(c_3358,plain,
    ( r2_hidden(k1_xboole_0,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3353,c_2355])).

cnf(c_1285,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2366,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2307,c_1285])).

cnf(c_3360,plain,
    ( r2_hidden(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3353,c_2366])).

cnf(c_3414,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3358,c_3360])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.34  % Running in FOF mode
% 3.04/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/0.96  
% 3.04/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.96  
% 3.04/0.96  ------  iProver source info
% 3.04/0.96  
% 3.04/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.96  git: non_committed_changes: false
% 3.04/0.96  git: last_make_outside_of_git: false
% 3.04/0.96  
% 3.04/0.96  ------ 
% 3.04/0.96  
% 3.04/0.96  ------ Input Options
% 3.04/0.96  
% 3.04/0.96  --out_options                           all
% 3.04/0.96  --tptp_safe_out                         true
% 3.04/0.96  --problem_path                          ""
% 3.04/0.96  --include_path                          ""
% 3.04/0.96  --clausifier                            res/vclausify_rel
% 3.04/0.96  --clausifier_options                    --mode clausify
% 3.04/0.96  --stdin                                 false
% 3.04/0.96  --stats_out                             all
% 3.04/0.96  
% 3.04/0.96  ------ General Options
% 3.04/0.96  
% 3.04/0.96  --fof                                   false
% 3.04/0.96  --time_out_real                         305.
% 3.04/0.96  --time_out_virtual                      -1.
% 3.04/0.96  --symbol_type_check                     false
% 3.04/0.96  --clausify_out                          false
% 3.04/0.96  --sig_cnt_out                           false
% 3.04/0.96  --trig_cnt_out                          false
% 3.04/0.96  --trig_cnt_out_tolerance                1.
% 3.04/0.96  --trig_cnt_out_sk_spl                   false
% 3.04/0.96  --abstr_cl_out                          false
% 3.04/0.96  
% 3.04/0.96  ------ Global Options
% 3.04/0.96  
% 3.04/0.96  --schedule                              default
% 3.04/0.96  --add_important_lit                     false
% 3.04/0.96  --prop_solver_per_cl                    1000
% 3.04/0.96  --min_unsat_core                        false
% 3.04/0.96  --soft_assumptions                      false
% 3.04/0.96  --soft_lemma_size                       3
% 3.04/0.96  --prop_impl_unit_size                   0
% 3.04/0.96  --prop_impl_unit                        []
% 3.04/0.96  --share_sel_clauses                     true
% 3.04/0.96  --reset_solvers                         false
% 3.04/0.96  --bc_imp_inh                            [conj_cone]
% 3.04/0.96  --conj_cone_tolerance                   3.
% 3.04/0.96  --extra_neg_conj                        none
% 3.04/0.96  --large_theory_mode                     true
% 3.04/0.96  --prolific_symb_bound                   200
% 3.04/0.96  --lt_threshold                          2000
% 3.04/0.96  --clause_weak_htbl                      true
% 3.04/0.96  --gc_record_bc_elim                     false
% 3.04/0.96  
% 3.04/0.96  ------ Preprocessing Options
% 3.04/0.96  
% 3.04/0.96  --preprocessing_flag                    true
% 3.04/0.96  --time_out_prep_mult                    0.1
% 3.04/0.96  --splitting_mode                        input
% 3.04/0.96  --splitting_grd                         true
% 3.04/0.96  --splitting_cvd                         false
% 3.04/0.96  --splitting_cvd_svl                     false
% 3.04/0.96  --splitting_nvd                         32
% 3.04/0.96  --sub_typing                            true
% 3.04/0.96  --prep_gs_sim                           true
% 3.04/0.96  --prep_unflatten                        true
% 3.04/0.96  --prep_res_sim                          true
% 3.04/0.96  --prep_upred                            true
% 3.04/0.96  --prep_sem_filter                       exhaustive
% 3.04/0.96  --prep_sem_filter_out                   false
% 3.04/0.96  --pred_elim                             true
% 3.04/0.96  --res_sim_input                         true
% 3.04/0.96  --eq_ax_congr_red                       true
% 3.04/0.96  --pure_diseq_elim                       true
% 3.04/0.96  --brand_transform                       false
% 3.04/0.96  --non_eq_to_eq                          false
% 3.04/0.96  --prep_def_merge                        true
% 3.04/0.96  --prep_def_merge_prop_impl              false
% 3.04/0.96  --prep_def_merge_mbd                    true
% 3.04/0.96  --prep_def_merge_tr_red                 false
% 3.04/0.96  --prep_def_merge_tr_cl                  false
% 3.04/0.96  --smt_preprocessing                     true
% 3.04/0.96  --smt_ac_axioms                         fast
% 3.04/0.96  --preprocessed_out                      false
% 3.04/0.96  --preprocessed_stats                    false
% 3.04/0.96  
% 3.04/0.96  ------ Abstraction refinement Options
% 3.04/0.96  
% 3.04/0.96  --abstr_ref                             []
% 3.04/0.96  --abstr_ref_prep                        false
% 3.04/0.96  --abstr_ref_until_sat                   false
% 3.04/0.96  --abstr_ref_sig_restrict                funpre
% 3.04/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.96  --abstr_ref_under                       []
% 3.04/0.96  
% 3.04/0.96  ------ SAT Options
% 3.04/0.96  
% 3.04/0.96  --sat_mode                              false
% 3.04/0.96  --sat_fm_restart_options                ""
% 3.04/0.96  --sat_gr_def                            false
% 3.04/0.96  --sat_epr_types                         true
% 3.04/0.96  --sat_non_cyclic_types                  false
% 3.04/0.96  --sat_finite_models                     false
% 3.04/0.96  --sat_fm_lemmas                         false
% 3.04/0.96  --sat_fm_prep                           false
% 3.04/0.96  --sat_fm_uc_incr                        true
% 3.04/0.96  --sat_out_model                         small
% 3.04/0.96  --sat_out_clauses                       false
% 3.04/0.96  
% 3.04/0.96  ------ QBF Options
% 3.04/0.96  
% 3.04/0.96  --qbf_mode                              false
% 3.04/0.96  --qbf_elim_univ                         false
% 3.04/0.96  --qbf_dom_inst                          none
% 3.04/0.96  --qbf_dom_pre_inst                      false
% 3.04/0.96  --qbf_sk_in                             false
% 3.04/0.96  --qbf_pred_elim                         true
% 3.04/0.96  --qbf_split                             512
% 3.04/0.96  
% 3.04/0.96  ------ BMC1 Options
% 3.04/0.96  
% 3.04/0.96  --bmc1_incremental                      false
% 3.04/0.96  --bmc1_axioms                           reachable_all
% 3.04/0.96  --bmc1_min_bound                        0
% 3.04/0.96  --bmc1_max_bound                        -1
% 3.04/0.96  --bmc1_max_bound_default                -1
% 3.04/0.96  --bmc1_symbol_reachability              true
% 3.04/0.96  --bmc1_property_lemmas                  false
% 3.04/0.96  --bmc1_k_induction                      false
% 3.04/0.96  --bmc1_non_equiv_states                 false
% 3.04/0.96  --bmc1_deadlock                         false
% 3.04/0.96  --bmc1_ucm                              false
% 3.04/0.96  --bmc1_add_unsat_core                   none
% 3.04/0.96  --bmc1_unsat_core_children              false
% 3.04/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.96  --bmc1_out_stat                         full
% 3.04/0.96  --bmc1_ground_init                      false
% 3.04/0.96  --bmc1_pre_inst_next_state              false
% 3.04/0.96  --bmc1_pre_inst_state                   false
% 3.04/0.96  --bmc1_pre_inst_reach_state             false
% 3.04/0.96  --bmc1_out_unsat_core                   false
% 3.04/0.96  --bmc1_aig_witness_out                  false
% 3.04/0.96  --bmc1_verbose                          false
% 3.04/0.96  --bmc1_dump_clauses_tptp                false
% 3.04/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.96  --bmc1_dump_file                        -
% 3.04/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.96  --bmc1_ucm_extend_mode                  1
% 3.04/0.96  --bmc1_ucm_init_mode                    2
% 3.04/0.96  --bmc1_ucm_cone_mode                    none
% 3.04/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.96  --bmc1_ucm_relax_model                  4
% 3.04/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.96  --bmc1_ucm_layered_model                none
% 3.04/0.96  --bmc1_ucm_max_lemma_size               10
% 3.04/0.96  
% 3.04/0.96  ------ AIG Options
% 3.04/0.96  
% 3.04/0.96  --aig_mode                              false
% 3.04/0.96  
% 3.04/0.96  ------ Instantiation Options
% 3.04/0.96  
% 3.04/0.96  --instantiation_flag                    true
% 3.04/0.96  --inst_sos_flag                         false
% 3.04/0.96  --inst_sos_phase                        true
% 3.04/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.96  --inst_lit_sel_side                     num_symb
% 3.04/0.96  --inst_solver_per_active                1400
% 3.04/0.96  --inst_solver_calls_frac                1.
% 3.04/0.96  --inst_passive_queue_type               priority_queues
% 3.04/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.96  --inst_passive_queues_freq              [25;2]
% 3.04/0.96  --inst_dismatching                      true
% 3.04/0.96  --inst_eager_unprocessed_to_passive     true
% 3.04/0.96  --inst_prop_sim_given                   true
% 3.04/0.96  --inst_prop_sim_new                     false
% 3.04/0.96  --inst_subs_new                         false
% 3.04/0.96  --inst_eq_res_simp                      false
% 3.04/0.96  --inst_subs_given                       false
% 3.04/0.96  --inst_orphan_elimination               true
% 3.04/0.96  --inst_learning_loop_flag               true
% 3.04/0.96  --inst_learning_start                   3000
% 3.04/0.96  --inst_learning_factor                  2
% 3.04/0.96  --inst_start_prop_sim_after_learn       3
% 3.04/0.96  --inst_sel_renew                        solver
% 3.04/0.96  --inst_lit_activity_flag                true
% 3.04/0.96  --inst_restr_to_given                   false
% 3.04/0.96  --inst_activity_threshold               500
% 3.04/0.96  --inst_out_proof                        true
% 3.04/0.96  
% 3.04/0.96  ------ Resolution Options
% 3.04/0.96  
% 3.04/0.96  --resolution_flag                       true
% 3.04/0.96  --res_lit_sel                           adaptive
% 3.04/0.96  --res_lit_sel_side                      none
% 3.04/0.96  --res_ordering                          kbo
% 3.04/0.96  --res_to_prop_solver                    active
% 3.04/0.96  --res_prop_simpl_new                    false
% 3.04/0.96  --res_prop_simpl_given                  true
% 3.04/0.96  --res_passive_queue_type                priority_queues
% 3.04/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.96  --res_passive_queues_freq               [15;5]
% 3.04/0.96  --res_forward_subs                      full
% 3.04/0.96  --res_backward_subs                     full
% 3.04/0.96  --res_forward_subs_resolution           true
% 3.04/0.96  --res_backward_subs_resolution          true
% 3.04/0.96  --res_orphan_elimination                true
% 3.04/0.96  --res_time_limit                        2.
% 3.04/0.96  --res_out_proof                         true
% 3.04/0.96  
% 3.04/0.96  ------ Superposition Options
% 3.04/0.96  
% 3.04/0.96  --superposition_flag                    true
% 3.04/0.96  --sup_passive_queue_type                priority_queues
% 3.04/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.96  --demod_completeness_check              fast
% 3.04/0.96  --demod_use_ground                      true
% 3.04/0.96  --sup_to_prop_solver                    passive
% 3.04/0.96  --sup_prop_simpl_new                    true
% 3.04/0.96  --sup_prop_simpl_given                  true
% 3.04/0.96  --sup_fun_splitting                     false
% 3.04/0.96  --sup_smt_interval                      50000
% 3.04/0.96  
% 3.04/0.96  ------ Superposition Simplification Setup
% 3.04/0.96  
% 3.04/0.96  --sup_indices_passive                   []
% 3.04/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.96  --sup_full_bw                           [BwDemod]
% 3.04/0.96  --sup_immed_triv                        [TrivRules]
% 3.04/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.96  --sup_immed_bw_main                     []
% 3.04/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.96  
% 3.04/0.96  ------ Combination Options
% 3.04/0.96  
% 3.04/0.96  --comb_res_mult                         3
% 3.04/0.96  --comb_sup_mult                         2
% 3.04/0.96  --comb_inst_mult                        10
% 3.04/0.96  
% 3.04/0.96  ------ Debug Options
% 3.04/0.96  
% 3.04/0.96  --dbg_backtrace                         false
% 3.04/0.96  --dbg_dump_prop_clauses                 false
% 3.04/0.96  --dbg_dump_prop_clauses_file            -
% 3.04/0.96  --dbg_out_stat                          false
% 3.04/0.96  ------ Parsing...
% 3.04/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.96  
% 3.04/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.04/0.96  
% 3.04/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.96  
% 3.04/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.96  ------ Proving...
% 3.04/0.96  ------ Problem Properties 
% 3.04/0.96  
% 3.04/0.96  
% 3.04/0.96  clauses                                 20
% 3.04/0.96  conjectures                             2
% 3.04/0.96  EPR                                     3
% 3.04/0.96  Horn                                    16
% 3.04/0.96  unary                                   7
% 3.04/0.96  binary                                  9
% 3.04/0.96  lits                                    38
% 3.04/0.96  lits eq                                 8
% 3.04/0.96  fd_pure                                 0
% 3.04/0.96  fd_pseudo                               0
% 3.04/0.96  fd_cond                                 1
% 3.04/0.96  fd_pseudo_cond                          2
% 3.04/0.96  AC symbols                              0
% 3.04/0.96  
% 3.04/0.96  ------ Schedule dynamic 5 is on 
% 3.04/0.96  
% 3.04/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.96  
% 3.04/0.96  
% 3.04/0.96  ------ 
% 3.04/0.96  Current options:
% 3.04/0.96  ------ 
% 3.04/0.96  
% 3.04/0.96  ------ Input Options
% 3.04/0.96  
% 3.04/0.96  --out_options                           all
% 3.04/0.96  --tptp_safe_out                         true
% 3.04/0.96  --problem_path                          ""
% 3.04/0.96  --include_path                          ""
% 3.04/0.96  --clausifier                            res/vclausify_rel
% 3.04/0.96  --clausifier_options                    --mode clausify
% 3.04/0.96  --stdin                                 false
% 3.04/0.96  --stats_out                             all
% 3.04/0.96  
% 3.04/0.96  ------ General Options
% 3.04/0.96  
% 3.04/0.96  --fof                                   false
% 3.04/0.96  --time_out_real                         305.
% 3.04/0.96  --time_out_virtual                      -1.
% 3.04/0.96  --symbol_type_check                     false
% 3.04/0.96  --clausify_out                          false
% 3.04/0.96  --sig_cnt_out                           false
% 3.04/0.96  --trig_cnt_out                          false
% 3.04/0.96  --trig_cnt_out_tolerance                1.
% 3.04/0.96  --trig_cnt_out_sk_spl                   false
% 3.04/0.96  --abstr_cl_out                          false
% 3.04/0.96  
% 3.04/0.96  ------ Global Options
% 3.04/0.96  
% 3.04/0.96  --schedule                              default
% 3.04/0.96  --add_important_lit                     false
% 3.04/0.96  --prop_solver_per_cl                    1000
% 3.04/0.96  --min_unsat_core                        false
% 3.04/0.96  --soft_assumptions                      false
% 3.04/0.96  --soft_lemma_size                       3
% 3.04/0.96  --prop_impl_unit_size                   0
% 3.04/0.96  --prop_impl_unit                        []
% 3.04/0.96  --share_sel_clauses                     true
% 3.04/0.96  --reset_solvers                         false
% 3.04/0.96  --bc_imp_inh                            [conj_cone]
% 3.04/0.96  --conj_cone_tolerance                   3.
% 3.04/0.96  --extra_neg_conj                        none
% 3.04/0.96  --large_theory_mode                     true
% 3.04/0.96  --prolific_symb_bound                   200
% 3.04/0.96  --lt_threshold                          2000
% 3.04/0.96  --clause_weak_htbl                      true
% 3.04/0.96  --gc_record_bc_elim                     false
% 3.04/0.96  
% 3.04/0.96  ------ Preprocessing Options
% 3.04/0.96  
% 3.04/0.96  --preprocessing_flag                    true
% 3.04/0.96  --time_out_prep_mult                    0.1
% 3.04/0.96  --splitting_mode                        input
% 3.04/0.96  --splitting_grd                         true
% 3.04/0.96  --splitting_cvd                         false
% 3.04/0.96  --splitting_cvd_svl                     false
% 3.04/0.96  --splitting_nvd                         32
% 3.04/0.96  --sub_typing                            true
% 3.04/0.96  --prep_gs_sim                           true
% 3.04/0.96  --prep_unflatten                        true
% 3.04/0.96  --prep_res_sim                          true
% 3.04/0.96  --prep_upred                            true
% 3.04/0.96  --prep_sem_filter                       exhaustive
% 3.04/0.96  --prep_sem_filter_out                   false
% 3.04/0.96  --pred_elim                             true
% 3.04/0.96  --res_sim_input                         true
% 3.04/0.96  --eq_ax_congr_red                       true
% 3.04/0.96  --pure_diseq_elim                       true
% 3.04/0.96  --brand_transform                       false
% 3.04/0.96  --non_eq_to_eq                          false
% 3.04/0.96  --prep_def_merge                        true
% 3.04/0.96  --prep_def_merge_prop_impl              false
% 3.04/0.96  --prep_def_merge_mbd                    true
% 3.04/0.96  --prep_def_merge_tr_red                 false
% 3.04/0.96  --prep_def_merge_tr_cl                  false
% 3.04/0.96  --smt_preprocessing                     true
% 3.04/0.96  --smt_ac_axioms                         fast
% 3.04/0.96  --preprocessed_out                      false
% 3.04/0.96  --preprocessed_stats                    false
% 3.04/0.96  
% 3.04/0.96  ------ Abstraction refinement Options
% 3.04/0.96  
% 3.04/0.96  --abstr_ref                             []
% 3.04/0.96  --abstr_ref_prep                        false
% 3.04/0.96  --abstr_ref_until_sat                   false
% 3.04/0.96  --abstr_ref_sig_restrict                funpre
% 3.04/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.96  --abstr_ref_under                       []
% 3.04/0.96  
% 3.04/0.96  ------ SAT Options
% 3.04/0.96  
% 3.04/0.96  --sat_mode                              false
% 3.04/0.96  --sat_fm_restart_options                ""
% 3.04/0.96  --sat_gr_def                            false
% 3.04/0.96  --sat_epr_types                         true
% 3.04/0.96  --sat_non_cyclic_types                  false
% 3.04/0.96  --sat_finite_models                     false
% 3.04/0.96  --sat_fm_lemmas                         false
% 3.04/0.96  --sat_fm_prep                           false
% 3.04/0.96  --sat_fm_uc_incr                        true
% 3.04/0.96  --sat_out_model                         small
% 3.04/0.96  --sat_out_clauses                       false
% 3.04/0.96  
% 3.04/0.96  ------ QBF Options
% 3.04/0.96  
% 3.04/0.96  --qbf_mode                              false
% 3.04/0.96  --qbf_elim_univ                         false
% 3.04/0.96  --qbf_dom_inst                          none
% 3.04/0.96  --qbf_dom_pre_inst                      false
% 3.04/0.96  --qbf_sk_in                             false
% 3.04/0.96  --qbf_pred_elim                         true
% 3.04/0.96  --qbf_split                             512
% 3.04/0.96  
% 3.04/0.96  ------ BMC1 Options
% 3.04/0.96  
% 3.04/0.96  --bmc1_incremental                      false
% 3.04/0.96  --bmc1_axioms                           reachable_all
% 3.04/0.96  --bmc1_min_bound                        0
% 3.04/0.96  --bmc1_max_bound                        -1
% 3.04/0.96  --bmc1_max_bound_default                -1
% 3.04/0.96  --bmc1_symbol_reachability              true
% 3.04/0.96  --bmc1_property_lemmas                  false
% 3.04/0.96  --bmc1_k_induction                      false
% 3.04/0.96  --bmc1_non_equiv_states                 false
% 3.04/0.96  --bmc1_deadlock                         false
% 3.04/0.96  --bmc1_ucm                              false
% 3.04/0.96  --bmc1_add_unsat_core                   none
% 3.04/0.96  --bmc1_unsat_core_children              false
% 3.04/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.96  --bmc1_out_stat                         full
% 3.04/0.96  --bmc1_ground_init                      false
% 3.04/0.96  --bmc1_pre_inst_next_state              false
% 3.04/0.96  --bmc1_pre_inst_state                   false
% 3.04/0.96  --bmc1_pre_inst_reach_state             false
% 3.04/0.96  --bmc1_out_unsat_core                   false
% 3.04/0.96  --bmc1_aig_witness_out                  false
% 3.04/0.96  --bmc1_verbose                          false
% 3.04/0.96  --bmc1_dump_clauses_tptp                false
% 3.04/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.96  --bmc1_dump_file                        -
% 3.04/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.96  --bmc1_ucm_extend_mode                  1
% 3.04/0.96  --bmc1_ucm_init_mode                    2
% 3.04/0.96  --bmc1_ucm_cone_mode                    none
% 3.04/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.96  --bmc1_ucm_relax_model                  4
% 3.04/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.96  --bmc1_ucm_layered_model                none
% 3.04/0.96  --bmc1_ucm_max_lemma_size               10
% 3.04/0.96  
% 3.04/0.96  ------ AIG Options
% 3.04/0.96  
% 3.04/0.96  --aig_mode                              false
% 3.04/0.96  
% 3.04/0.96  ------ Instantiation Options
% 3.04/0.96  
% 3.04/0.96  --instantiation_flag                    true
% 3.04/0.96  --inst_sos_flag                         false
% 3.04/0.96  --inst_sos_phase                        true
% 3.04/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.96  --inst_lit_sel_side                     none
% 3.04/0.96  --inst_solver_per_active                1400
% 3.04/0.96  --inst_solver_calls_frac                1.
% 3.04/0.96  --inst_passive_queue_type               priority_queues
% 3.04/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.96  --inst_passive_queues_freq              [25;2]
% 3.04/0.96  --inst_dismatching                      true
% 3.04/0.96  --inst_eager_unprocessed_to_passive     true
% 3.04/0.96  --inst_prop_sim_given                   true
% 3.04/0.96  --inst_prop_sim_new                     false
% 3.04/0.96  --inst_subs_new                         false
% 3.04/0.96  --inst_eq_res_simp                      false
% 3.04/0.96  --inst_subs_given                       false
% 3.04/0.96  --inst_orphan_elimination               true
% 3.04/0.96  --inst_learning_loop_flag               true
% 3.04/0.96  --inst_learning_start                   3000
% 3.04/0.96  --inst_learning_factor                  2
% 3.04/0.96  --inst_start_prop_sim_after_learn       3
% 3.04/0.96  --inst_sel_renew                        solver
% 3.04/0.96  --inst_lit_activity_flag                true
% 3.04/0.96  --inst_restr_to_given                   false
% 3.04/0.96  --inst_activity_threshold               500
% 3.04/0.96  --inst_out_proof                        true
% 3.04/0.96  
% 3.04/0.96  ------ Resolution Options
% 3.04/0.96  
% 3.04/0.96  --resolution_flag                       false
% 3.04/0.96  --res_lit_sel                           adaptive
% 3.04/0.96  --res_lit_sel_side                      none
% 3.04/0.96  --res_ordering                          kbo
% 3.04/0.96  --res_to_prop_solver                    active
% 3.04/0.96  --res_prop_simpl_new                    false
% 3.04/0.96  --res_prop_simpl_given                  true
% 3.04/0.96  --res_passive_queue_type                priority_queues
% 3.04/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.96  --res_passive_queues_freq               [15;5]
% 3.04/0.96  --res_forward_subs                      full
% 3.04/0.96  --res_backward_subs                     full
% 3.04/0.96  --res_forward_subs_resolution           true
% 3.04/0.96  --res_backward_subs_resolution          true
% 3.04/0.96  --res_orphan_elimination                true
% 3.04/0.96  --res_time_limit                        2.
% 3.04/0.96  --res_out_proof                         true
% 3.04/0.96  
% 3.04/0.96  ------ Superposition Options
% 3.04/0.96  
% 3.04/0.96  --superposition_flag                    true
% 3.04/0.96  --sup_passive_queue_type                priority_queues
% 3.04/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.96  --demod_completeness_check              fast
% 3.04/0.96  --demod_use_ground                      true
% 3.04/0.96  --sup_to_prop_solver                    passive
% 3.04/0.96  --sup_prop_simpl_new                    true
% 3.04/0.96  --sup_prop_simpl_given                  true
% 3.04/0.96  --sup_fun_splitting                     false
% 3.04/0.96  --sup_smt_interval                      50000
% 3.04/0.96  
% 3.04/0.96  ------ Superposition Simplification Setup
% 3.04/0.96  
% 3.04/0.96  --sup_indices_passive                   []
% 3.04/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.96  --sup_full_bw                           [BwDemod]
% 3.04/0.96  --sup_immed_triv                        [TrivRules]
% 3.04/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.96  --sup_immed_bw_main                     []
% 3.04/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.96  
% 3.04/0.96  ------ Combination Options
% 3.04/0.96  
% 3.04/0.96  --comb_res_mult                         3
% 3.04/0.96  --comb_sup_mult                         2
% 3.04/0.96  --comb_inst_mult                        10
% 3.04/0.96  
% 3.04/0.96  ------ Debug Options
% 3.04/0.96  
% 3.04/0.96  --dbg_backtrace                         false
% 3.04/0.96  --dbg_dump_prop_clauses                 false
% 3.04/0.96  --dbg_dump_prop_clauses_file            -
% 3.04/0.96  --dbg_out_stat                          false
% 3.04/0.96  
% 3.04/0.96  
% 3.04/0.96  
% 3.04/0.96  
% 3.04/0.96  ------ Proving...
% 3.04/0.96  
% 3.04/0.96  
% 3.04/0.96  % SZS status Theorem for theBenchmark.p
% 3.04/0.96  
% 3.04/0.96   Resolution empty clause
% 3.04/0.96  
% 3.04/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.96  
% 3.04/0.96  fof(f11,axiom,(
% 3.04/0.96    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f54,plain,(
% 3.04/0.96    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.04/0.96    inference(cnf_transformation,[],[f11])).
% 3.04/0.96  
% 3.04/0.96  fof(f10,axiom,(
% 3.04/0.96    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f25,plain,(
% 3.04/0.96    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.04/0.96    inference(ennf_transformation,[],[f10])).
% 3.04/0.96  
% 3.04/0.96  fof(f53,plain,(
% 3.04/0.96    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f25])).
% 3.04/0.96  
% 3.04/0.96  fof(f13,axiom,(
% 3.04/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f27,plain,(
% 3.04/0.96    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.04/0.96    inference(ennf_transformation,[],[f13])).
% 3.04/0.96  
% 3.04/0.96  fof(f28,plain,(
% 3.04/0.96    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/0.96    inference(flattening,[],[f27])).
% 3.04/0.96  
% 3.04/0.96  fof(f39,plain,(
% 3.04/0.96    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/0.96    inference(nnf_transformation,[],[f28])).
% 3.04/0.96  
% 3.04/0.96  fof(f60,plain,(
% 3.04/0.96    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f39])).
% 3.04/0.96  
% 3.04/0.96  fof(f80,plain,(
% 3.04/0.96    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.96    inference(equality_resolution,[],[f60])).
% 3.04/0.96  
% 3.04/0.96  fof(f12,axiom,(
% 3.04/0.96    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f26,plain,(
% 3.04/0.96    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.04/0.96    inference(ennf_transformation,[],[f12])).
% 3.04/0.96  
% 3.04/0.96  fof(f56,plain,(
% 3.04/0.96    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f26])).
% 3.04/0.96  
% 3.04/0.96  fof(f1,axiom,(
% 3.04/0.96    v1_xboole_0(k1_xboole_0)),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f44,plain,(
% 3.04/0.96    v1_xboole_0(k1_xboole_0)),
% 3.04/0.96    inference(cnf_transformation,[],[f1])).
% 3.04/0.96  
% 3.04/0.96  fof(f57,plain,(
% 3.04/0.96    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f39])).
% 3.04/0.96  
% 3.04/0.96  fof(f82,plain,(
% 3.04/0.96    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.96    inference(equality_resolution,[],[f57])).
% 3.04/0.96  
% 3.04/0.96  fof(f2,axiom,(
% 3.04/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f45,plain,(
% 3.04/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f2])).
% 3.04/0.96  
% 3.04/0.96  fof(f14,axiom,(
% 3.04/0.96    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f29,plain,(
% 3.04/0.96    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.04/0.96    inference(ennf_transformation,[],[f14])).
% 3.04/0.96  
% 3.04/0.96  fof(f61,plain,(
% 3.04/0.96    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f29])).
% 3.04/0.96  
% 3.04/0.96  fof(f17,axiom,(
% 3.04/0.96    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f21,plain,(
% 3.04/0.96    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.04/0.96    inference(pure_predicate_removal,[],[f17])).
% 3.04/0.96  
% 3.04/0.96  fof(f32,plain,(
% 3.04/0.96    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.04/0.96    inference(ennf_transformation,[],[f21])).
% 3.04/0.96  
% 3.04/0.96  fof(f40,plain,(
% 3.04/0.96    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.04/0.96    introduced(choice_axiom,[])).
% 3.04/0.96  
% 3.04/0.96  fof(f41,plain,(
% 3.04/0.96    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.04/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f40])).
% 3.04/0.96  
% 3.04/0.96  fof(f66,plain,(
% 3.04/0.96    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.04/0.96    inference(cnf_transformation,[],[f41])).
% 3.04/0.96  
% 3.04/0.96  fof(f8,axiom,(
% 3.04/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f22,plain,(
% 3.04/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.04/0.96    inference(ennf_transformation,[],[f8])).
% 3.04/0.96  
% 3.04/0.96  fof(f51,plain,(
% 3.04/0.96    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.04/0.96    inference(cnf_transformation,[],[f22])).
% 3.04/0.96  
% 3.04/0.96  fof(f19,conjecture,(
% 3.04/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f20,negated_conjecture,(
% 3.04/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 3.04/0.96    inference(negated_conjecture,[],[f19])).
% 3.04/0.96  
% 3.04/0.96  fof(f35,plain,(
% 3.04/0.96    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.04/0.96    inference(ennf_transformation,[],[f20])).
% 3.04/0.96  
% 3.04/0.96  fof(f36,plain,(
% 3.04/0.96    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.04/0.96    inference(flattening,[],[f35])).
% 3.04/0.96  
% 3.04/0.96  fof(f42,plain,(
% 3.04/0.96    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 3.04/0.96    introduced(choice_axiom,[])).
% 3.04/0.96  
% 3.04/0.96  fof(f43,plain,(
% 3.04/0.96    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 3.04/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f42])).
% 3.04/0.96  
% 3.04/0.96  fof(f70,plain,(
% 3.04/0.96    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 3.04/0.96    inference(cnf_transformation,[],[f43])).
% 3.04/0.96  
% 3.04/0.96  fof(f3,axiom,(
% 3.04/0.96    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f46,plain,(
% 3.04/0.96    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f3])).
% 3.04/0.96  
% 3.04/0.96  fof(f4,axiom,(
% 3.04/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f47,plain,(
% 3.04/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f4])).
% 3.04/0.96  
% 3.04/0.96  fof(f5,axiom,(
% 3.04/0.96    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f48,plain,(
% 3.04/0.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f5])).
% 3.04/0.96  
% 3.04/0.96  fof(f73,plain,(
% 3.04/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.04/0.96    inference(definition_unfolding,[],[f47,f48])).
% 3.04/0.96  
% 3.04/0.96  fof(f74,plain,(
% 3.04/0.96    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.04/0.96    inference(definition_unfolding,[],[f46,f73])).
% 3.04/0.96  
% 3.04/0.96  fof(f78,plain,(
% 3.04/0.96    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 3.04/0.96    inference(definition_unfolding,[],[f70,f74])).
% 3.04/0.96  
% 3.04/0.96  fof(f16,axiom,(
% 3.04/0.96    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f31,plain,(
% 3.04/0.96    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 3.04/0.96    inference(ennf_transformation,[],[f16])).
% 3.04/0.96  
% 3.04/0.96  fof(f64,plain,(
% 3.04/0.96    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 3.04/0.96    inference(cnf_transformation,[],[f31])).
% 3.04/0.96  
% 3.04/0.96  fof(f77,plain,(
% 3.04/0.96    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))) )),
% 3.04/0.96    inference(definition_unfolding,[],[f64,f74])).
% 3.04/0.96  
% 3.04/0.96  fof(f15,axiom,(
% 3.04/0.96    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f30,plain,(
% 3.04/0.96    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.04/0.96    inference(ennf_transformation,[],[f15])).
% 3.04/0.96  
% 3.04/0.96  fof(f62,plain,(
% 3.04/0.96    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.04/0.96    inference(cnf_transformation,[],[f30])).
% 3.04/0.96  
% 3.04/0.96  fof(f18,axiom,(
% 3.04/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f33,plain,(
% 3.04/0.96    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.04/0.96    inference(ennf_transformation,[],[f18])).
% 3.04/0.96  
% 3.04/0.96  fof(f34,plain,(
% 3.04/0.96    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.04/0.96    inference(flattening,[],[f33])).
% 3.04/0.96  
% 3.04/0.96  fof(f67,plain,(
% 3.04/0.96    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f34])).
% 3.04/0.96  
% 3.04/0.96  fof(f69,plain,(
% 3.04/0.96    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 3.04/0.96    inference(cnf_transformation,[],[f43])).
% 3.04/0.96  
% 3.04/0.96  fof(f79,plain,(
% 3.04/0.96    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 3.04/0.96    inference(definition_unfolding,[],[f69,f74])).
% 3.04/0.96  
% 3.04/0.96  fof(f68,plain,(
% 3.04/0.96    v1_funct_1(sK4)),
% 3.04/0.96    inference(cnf_transformation,[],[f43])).
% 3.04/0.96  
% 3.04/0.96  fof(f71,plain,(
% 3.04/0.96    k1_xboole_0 != sK3),
% 3.04/0.96    inference(cnf_transformation,[],[f43])).
% 3.04/0.96  
% 3.04/0.96  fof(f72,plain,(
% 3.04/0.96    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 3.04/0.96    inference(cnf_transformation,[],[f43])).
% 3.04/0.96  
% 3.04/0.96  fof(f7,axiom,(
% 3.04/0.96    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f37,plain,(
% 3.04/0.96    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 3.04/0.96    introduced(choice_axiom,[])).
% 3.04/0.96  
% 3.04/0.96  fof(f38,plain,(
% 3.04/0.96    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 3.04/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f37])).
% 3.04/0.96  
% 3.04/0.96  fof(f50,plain,(
% 3.04/0.96    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f38])).
% 3.04/0.96  
% 3.04/0.96  fof(f9,axiom,(
% 3.04/0.96    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f23,plain,(
% 3.04/0.96    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.04/0.96    inference(ennf_transformation,[],[f9])).
% 3.04/0.96  
% 3.04/0.96  fof(f24,plain,(
% 3.04/0.96    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.04/0.96    inference(flattening,[],[f23])).
% 3.04/0.96  
% 3.04/0.96  fof(f52,plain,(
% 3.04/0.96    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.04/0.96    inference(cnf_transformation,[],[f24])).
% 3.04/0.96  
% 3.04/0.96  fof(f6,axiom,(
% 3.04/0.96    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 3.04/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.96  
% 3.04/0.96  fof(f49,plain,(
% 3.04/0.96    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 3.04/0.96    inference(cnf_transformation,[],[f6])).
% 3.04/0.96  
% 3.04/0.96  fof(f75,plain,(
% 3.04/0.96    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 3.04/0.96    inference(definition_unfolding,[],[f49,f73])).
% 3.04/0.96  
% 3.04/0.96  cnf(c_8,plain,
% 3.04/0.96      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.04/0.96      inference(cnf_transformation,[],[f54]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_6,plain,
% 3.04/0.96      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.04/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_10,plain,
% 3.04/0.96      ( r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | ~ v1_funct_1(X1)
% 3.04/0.96      | ~ v1_relat_1(X1)
% 3.04/0.96      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 3.04/0.96      inference(cnf_transformation,[],[f80]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_492,plain,
% 3.04/0.96      ( r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | ~ v1_funct_1(X1)
% 3.04/0.96      | ~ v1_xboole_0(X2)
% 3.04/0.96      | X1 != X2
% 3.04/0.96      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 3.04/0.96      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_493,plain,
% 3.04/0.96      ( r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | ~ v1_funct_1(X1)
% 3.04/0.96      | ~ v1_xboole_0(X1)
% 3.04/0.96      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 3.04/0.96      inference(unflattening,[status(thm)],[c_492]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_9,plain,
% 3.04/0.96      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.04/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_505,plain,
% 3.04/0.96      ( r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | ~ v1_xboole_0(X1)
% 3.04/0.96      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 3.04/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_493,c_9]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1276,plain,
% 3.04/0.96      ( k1_funct_1(X0,X1) = k1_xboole_0
% 3.04/0.96      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 3.04/0.96      | v1_xboole_0(X0) != iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_3350,plain,
% 3.04/0.96      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0
% 3.04/0.96      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 3.04/0.96      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.04/0.96      inference(superposition,[status(thm)],[c_8,c_1276]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_0,plain,
% 3.04/0.96      ( v1_xboole_0(k1_xboole_0) ),
% 3.04/0.96      inference(cnf_transformation,[],[f44]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_13,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.04/0.96      | ~ v1_funct_1(X1)
% 3.04/0.96      | ~ v1_relat_1(X1) ),
% 3.04/0.96      inference(cnf_transformation,[],[f82]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_449,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.04/0.96      | ~ v1_funct_1(X1)
% 3.04/0.96      | ~ v1_xboole_0(X2)
% 3.04/0.96      | X1 != X2 ),
% 3.04/0.96      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_450,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.04/0.96      | ~ v1_funct_1(X1)
% 3.04/0.96      | ~ v1_xboole_0(X1) ),
% 3.04/0.96      inference(unflattening,[status(thm)],[c_449]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_462,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.04/0.96      | ~ v1_xboole_0(X1) ),
% 3.04/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_450,c_9]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_546,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.04/0.96      | k1_xboole_0 != X1 ),
% 3.04/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_462]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_547,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 3.04/0.96      | r2_hidden(k4_tarski(X0,k1_funct_1(k1_xboole_0,X0)),k1_xboole_0) ),
% 3.04/0.96      inference(unflattening,[status(thm)],[c_546]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1,plain,
% 3.04/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 3.04/0.96      inference(cnf_transformation,[],[f45]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_14,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.04/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_262,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.04/0.96      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_263,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.04/0.96      inference(unflattening,[status(thm)],[c_262]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_555,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
% 3.04/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_547,c_263]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_529,plain,
% 3.04/0.96      ( r2_hidden(X0,k1_relat_1(X1))
% 3.04/0.96      | k1_funct_1(X1,X0) = k1_xboole_0
% 3.04/0.96      | k1_xboole_0 != X1 ),
% 3.04/0.96      inference(resolution_lifted,[status(thm)],[c_0,c_505]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_530,plain,
% 3.04/0.96      ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
% 3.04/0.96      | k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.04/0.96      inference(unflattening,[status(thm)],[c_529]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_557,plain,
% 3.04/0.96      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.04/0.96      inference(backward_subsumption_resolution,[status(thm)],[c_555,c_530]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_3353,plain,
% 3.04/0.96      ( k1_funct_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.04/0.96      inference(global_propositional_subsumption,[status(thm)],[c_3350,c_557]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_19,plain,
% 3.04/0.96      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.04/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1286,plain,
% 3.04/0.96      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_4,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,X1)
% 3.04/0.96      | r2_hidden(X0,X2)
% 3.04/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.04/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_23,negated_conjecture,
% 3.04/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 3.04/0.96      inference(cnf_transformation,[],[f78]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_316,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,X1)
% 3.04/0.96      | r2_hidden(X0,X2)
% 3.04/0.96      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X2)
% 3.04/0.96      | sK4 != X1 ),
% 3.04/0.96      inference(resolution_lifted,[status(thm)],[c_4,c_23]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_317,plain,
% 3.04/0.96      ( r2_hidden(X0,X1)
% 3.04/0.96      | ~ r2_hidden(X0,sK4)
% 3.04/0.96      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X1) ),
% 3.04/0.96      inference(unflattening,[status(thm)],[c_316]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1280,plain,
% 3.04/0.96      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
% 3.04/0.96      | r2_hidden(X1,X0) = iProver_top
% 3.04/0.96      | r2_hidden(X1,sK4) != iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1419,plain,
% 3.04/0.96      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top
% 3.04/0.96      | r2_hidden(X0,sK4) != iProver_top ),
% 3.04/0.96      inference(equality_resolution,[status(thm)],[c_1280]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_18,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
% 3.04/0.96      | k1_mcart_1(X0) = X1 ),
% 3.04/0.96      inference(cnf_transformation,[],[f77]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1287,plain,
% 3.04/0.96      ( k1_mcart_1(X0) = X1
% 3.04/0.96      | r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) != iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2017,plain,
% 3.04/0.96      ( k1_mcart_1(X0) = sK2 | r2_hidden(X0,sK4) != iProver_top ),
% 3.04/0.96      inference(superposition,[status(thm)],[c_1419,c_1287]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2077,plain,
% 3.04/0.96      ( k1_mcart_1(sK1(sK4)) = sK2 | sK4 = k1_xboole_0 ),
% 3.04/0.96      inference(superposition,[status(thm)],[c_1286,c_2017]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_16,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.04/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1289,plain,
% 3.04/0.96      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.04/0.96      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1725,plain,
% 3.04/0.96      ( r2_hidden(X0,sK4) != iProver_top
% 3.04/0.96      | r2_hidden(k1_mcart_1(X0),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.04/0.96      inference(superposition,[status(thm)],[c_1419,c_1289]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_20,plain,
% 3.04/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.96      | ~ r2_hidden(X3,X1)
% 3.04/0.96      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.04/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.96      | ~ v1_funct_1(X0)
% 3.04/0.96      | k1_xboole_0 = X2 ),
% 3.04/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_24,negated_conjecture,
% 3.04/0.96      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 3.04/0.96      inference(cnf_transformation,[],[f79]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_273,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,X1)
% 3.04/0.96      | r2_hidden(k1_funct_1(X2,X0),X3)
% 3.04/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.04/0.96      | ~ v1_funct_1(X2)
% 3.04/0.96      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 3.04/0.96      | sK3 != X3
% 3.04/0.96      | sK4 != X2
% 3.04/0.96      | k1_xboole_0 = X3 ),
% 3.04/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_274,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.04/0.96      | r2_hidden(k1_funct_1(sK4,X0),sK3)
% 3.04/0.96      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 3.04/0.96      | ~ v1_funct_1(sK4)
% 3.04/0.96      | k1_xboole_0 = sK3 ),
% 3.04/0.96      inference(unflattening,[status(thm)],[c_273]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_25,negated_conjecture,
% 3.04/0.96      ( v1_funct_1(sK4) ),
% 3.04/0.96      inference(cnf_transformation,[],[f68]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_22,negated_conjecture,
% 3.04/0.96      ( k1_xboole_0 != sK3 ),
% 3.04/0.96      inference(cnf_transformation,[],[f71]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_278,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(sK4,X0),sK3)
% 3.04/0.96      | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.04/0.96      inference(global_propositional_subsumption,
% 3.04/0.96                [status(thm)],
% 3.04/0.96                [c_274,c_25,c_23,c_22]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_279,plain,
% 3.04/0.96      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.04/0.96      | r2_hidden(k1_funct_1(sK4,X0),sK3) ),
% 3.04/0.96      inference(renaming,[status(thm)],[c_278]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1283,plain,
% 3.04/0.96      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 3.04/0.96      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1770,plain,
% 3.04/0.96      ( r2_hidden(X0,sK4) != iProver_top
% 3.04/0.96      | r2_hidden(k1_funct_1(sK4,k1_mcart_1(X0)),sK3) = iProver_top ),
% 3.04/0.96      inference(superposition,[status(thm)],[c_1725,c_1283]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2099,plain,
% 3.04/0.96      ( sK4 = k1_xboole_0
% 3.04/0.96      | r2_hidden(k1_funct_1(sK4,sK2),sK3) = iProver_top
% 3.04/0.96      | r2_hidden(sK1(sK4),sK4) != iProver_top ),
% 3.04/0.96      inference(superposition,[status(thm)],[c_2077,c_1770]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_21,negated_conjecture,
% 3.04/0.96      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 3.04/0.96      inference(cnf_transformation,[],[f72]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_29,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2301,plain,
% 3.04/0.96      ( sK4 = k1_xboole_0 | r2_hidden(sK1(sK4),sK4) != iProver_top ),
% 3.04/0.96      inference(global_propositional_subsumption,[status(thm)],[c_2099,c_29]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2307,plain,
% 3.04/0.96      ( sK4 = k1_xboole_0 ),
% 3.04/0.96      inference(superposition,[status(thm)],[c_1286,c_2301]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_3,plain,
% 3.04/0.96      ( m1_subset_1(sK0(X0),X0) ),
% 3.04/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_5,plain,
% 3.04/0.96      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.04/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_306,plain,
% 3.04/0.96      ( r2_hidden(X0,X1) | v1_xboole_0(X1) | X1 != X2 | sK0(X2) != X0 ),
% 3.04/0.96      inference(resolution_lifted,[status(thm)],[c_3,c_5]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_307,plain,
% 3.04/0.96      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.04/0.96      inference(unflattening,[status(thm)],[c_306]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1281,plain,
% 3.04/0.96      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1983,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top
% 3.04/0.96      | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.04/0.96      inference(superposition,[status(thm)],[c_1281,c_1283]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1406,plain,
% 3.04/0.96      ( r2_hidden(sK0(k2_enumset1(X0,X0,X0,X1)),k2_enumset1(X0,X0,X0,X1))
% 3.04/0.96      | v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 3.04/0.96      inference(instantiation,[status(thm)],[c_307]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1714,plain,
% 3.04/0.96      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2))
% 3.04/0.96      | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.04/0.96      inference(instantiation,[status(thm)],[c_1406]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1716,plain,
% 3.04/0.96      ( r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 3.04/0.96      | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1715,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3)
% 3.04/0.96      | ~ r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.04/0.96      inference(instantiation,[status(thm)],[c_279]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1718,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top
% 3.04/0.96      | r2_hidden(sK0(k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_1715]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2,plain,
% 3.04/0.96      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
% 3.04/0.96      inference(cnf_transformation,[],[f75]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1755,plain,
% 3.04/0.96      ( ~ v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.04/0.96      inference(instantiation,[status(thm)],[c_2]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1756,plain,
% 3.04/0.96      ( v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_1755]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2210,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 3.04/0.96      inference(global_propositional_subsumption,
% 3.04/0.96                [status(thm)],
% 3.04/0.96                [c_1983,c_1716,c_1718,c_1756]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2355,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),sK3) = iProver_top ),
% 3.04/0.96      inference(demodulation,[status(thm)],[c_2307,c_2210]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_3358,plain,
% 3.04/0.96      ( r2_hidden(k1_xboole_0,sK3) = iProver_top ),
% 3.04/0.96      inference(demodulation,[status(thm)],[c_3353,c_2355]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_1285,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 3.04/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_2366,plain,
% 3.04/0.96      ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),sK3) != iProver_top ),
% 3.04/0.96      inference(demodulation,[status(thm)],[c_2307,c_1285]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_3360,plain,
% 3.04/0.96      ( r2_hidden(k1_xboole_0,sK3) != iProver_top ),
% 3.04/0.96      inference(demodulation,[status(thm)],[c_3353,c_2366]) ).
% 3.04/0.96  
% 3.04/0.96  cnf(c_3414,plain,
% 3.04/0.96      ( $false ),
% 3.04/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_3358,c_3360]) ).
% 3.04/0.96  
% 3.04/0.96  
% 3.04/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.96  
% 3.04/0.96  ------                               Statistics
% 3.04/0.96  
% 3.04/0.96  ------ General
% 3.04/0.96  
% 3.04/0.96  abstr_ref_over_cycles:                  0
% 3.04/0.96  abstr_ref_under_cycles:                 0
% 3.04/0.96  gc_basic_clause_elim:                   0
% 3.04/0.96  forced_gc_time:                         0
% 3.04/0.96  parsing_time:                           0.011
% 3.04/0.96  unif_index_cands_time:                  0.
% 3.04/0.96  unif_index_add_time:                    0.
% 3.04/0.96  orderings_time:                         0.
% 3.04/0.96  out_proof_time:                         0.009
% 3.04/0.96  total_time:                             0.136
% 3.04/0.96  num_of_symbols:                         53
% 3.04/0.96  num_of_terms:                           2928
% 3.04/0.96  
% 3.04/0.96  ------ Preprocessing
% 3.04/0.96  
% 3.04/0.96  num_of_splits:                          0
% 3.04/0.96  num_of_split_atoms:                     0
% 3.04/0.96  num_of_reused_defs:                     0
% 3.04/0.96  num_eq_ax_congr_red:                    15
% 3.04/0.96  num_of_sem_filtered_clauses:            1
% 3.04/0.96  num_of_subtypes:                        0
% 3.04/0.96  monotx_restored_types:                  0
% 3.04/0.96  sat_num_of_epr_types:                   0
% 3.04/0.96  sat_num_of_non_cyclic_types:            0
% 3.04/0.96  sat_guarded_non_collapsed_types:        0
% 3.04/0.96  num_pure_diseq_elim:                    0
% 3.04/0.96  simp_replaced_by:                       0
% 3.04/0.96  res_preprocessed:                       110
% 3.04/0.96  prep_upred:                             0
% 3.04/0.96  prep_unflattend:                        40
% 3.04/0.96  smt_new_axioms:                         0
% 3.04/0.96  pred_elim_cands:                        2
% 3.04/0.96  pred_elim:                              5
% 3.04/0.96  pred_elim_cl:                           5
% 3.04/0.96  pred_elim_cycles:                       8
% 3.04/0.96  merged_defs:                            0
% 3.04/0.96  merged_defs_ncl:                        0
% 3.04/0.96  bin_hyper_res:                          0
% 3.04/0.96  prep_cycles:                            4
% 3.04/0.96  pred_elim_time:                         0.01
% 3.04/0.96  splitting_time:                         0.
% 3.04/0.96  sem_filter_time:                        0.
% 3.04/0.96  monotx_time:                            0.
% 3.04/0.96  subtype_inf_time:                       0.
% 3.04/0.96  
% 3.04/0.96  ------ Problem properties
% 3.04/0.96  
% 3.04/0.96  clauses:                                20
% 3.04/0.96  conjectures:                            2
% 3.04/0.96  epr:                                    3
% 3.04/0.96  horn:                                   16
% 3.04/0.96  ground:                                 6
% 3.04/0.96  unary:                                  7
% 3.04/0.96  binary:                                 9
% 3.04/0.96  lits:                                   38
% 3.04/0.96  lits_eq:                                8
% 3.04/0.96  fd_pure:                                0
% 3.04/0.96  fd_pseudo:                              0
% 3.04/0.96  fd_cond:                                1
% 3.04/0.96  fd_pseudo_cond:                         2
% 3.04/0.96  ac_symbols:                             0
% 3.04/0.96  
% 3.04/0.96  ------ Propositional Solver
% 3.04/0.96  
% 3.04/0.96  prop_solver_calls:                      28
% 3.04/0.96  prop_fast_solver_calls:                 678
% 3.04/0.96  smt_solver_calls:                       0
% 3.04/0.96  smt_fast_solver_calls:                  0
% 3.04/0.96  prop_num_of_clauses:                    969
% 3.04/0.96  prop_preprocess_simplified:             3974
% 3.04/0.96  prop_fo_subsumed:                       11
% 3.04/0.96  prop_solver_time:                       0.
% 3.04/0.96  smt_solver_time:                        0.
% 3.04/0.96  smt_fast_solver_time:                   0.
% 3.04/0.96  prop_fast_solver_time:                  0.
% 3.04/0.96  prop_unsat_core_time:                   0.
% 3.04/0.96  
% 3.04/0.96  ------ QBF
% 3.04/0.96  
% 3.04/0.96  qbf_q_res:                              0
% 3.04/0.96  qbf_num_tautologies:                    0
% 3.04/0.96  qbf_prep_cycles:                        0
% 3.04/0.96  
% 3.04/0.96  ------ BMC1
% 3.04/0.96  
% 3.04/0.96  bmc1_current_bound:                     -1
% 3.04/0.96  bmc1_last_solved_bound:                 -1
% 3.04/0.96  bmc1_unsat_core_size:                   -1
% 3.04/0.96  bmc1_unsat_core_parents_size:           -1
% 3.04/0.96  bmc1_merge_next_fun:                    0
% 3.04/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.96  
% 3.04/0.96  ------ Instantiation
% 3.04/0.96  
% 3.04/0.96  inst_num_of_clauses:                    278
% 3.04/0.96  inst_num_in_passive:                    89
% 3.04/0.96  inst_num_in_active:                     184
% 3.04/0.96  inst_num_in_unprocessed:                5
% 3.04/0.96  inst_num_of_loops:                      240
% 3.04/0.96  inst_num_of_learning_restarts:          0
% 3.04/0.96  inst_num_moves_active_passive:          53
% 3.04/0.96  inst_lit_activity:                      0
% 3.04/0.96  inst_lit_activity_moves:                0
% 3.04/0.96  inst_num_tautologies:                   0
% 3.04/0.96  inst_num_prop_implied:                  0
% 3.04/0.96  inst_num_existing_simplified:           0
% 3.04/0.96  inst_num_eq_res_simplified:             0
% 3.04/0.96  inst_num_child_elim:                    0
% 3.04/0.96  inst_num_of_dismatching_blockings:      39
% 3.04/0.96  inst_num_of_non_proper_insts:           254
% 3.04/0.96  inst_num_of_duplicates:                 0
% 3.04/0.96  inst_inst_num_from_inst_to_res:         0
% 3.04/0.96  inst_dismatching_checking_time:         0.
% 3.04/0.96  
% 3.04/0.96  ------ Resolution
% 3.04/0.96  
% 3.04/0.96  res_num_of_clauses:                     0
% 3.04/0.96  res_num_in_passive:                     0
% 3.04/0.96  res_num_in_active:                      0
% 3.04/0.96  res_num_of_loops:                       114
% 3.04/0.96  res_forward_subset_subsumed:            45
% 3.04/0.96  res_backward_subset_subsumed:           0
% 3.04/0.96  res_forward_subsumed:                   1
% 3.04/0.96  res_backward_subsumed:                  0
% 3.04/0.96  res_forward_subsumption_resolution:     4
% 3.04/0.96  res_backward_subsumption_resolution:    1
% 3.04/0.96  res_clause_to_clause_subsumption:       192
% 3.04/0.96  res_orphan_elimination:                 0
% 3.04/0.96  res_tautology_del:                      66
% 3.04/0.96  res_num_eq_res_simplified:              0
% 3.04/0.96  res_num_sel_changes:                    0
% 3.04/0.96  res_moves_from_active_to_pass:          0
% 3.04/0.96  
% 3.04/0.96  ------ Superposition
% 3.04/0.96  
% 3.04/0.96  sup_time_total:                         0.
% 3.04/0.96  sup_time_generating:                    0.
% 3.04/0.96  sup_time_sim_full:                      0.
% 3.04/0.96  sup_time_sim_immed:                     0.
% 3.04/0.96  
% 3.04/0.96  sup_num_of_clauses:                     69
% 3.04/0.96  sup_num_in_active:                      23
% 3.04/0.96  sup_num_in_passive:                     46
% 3.04/0.96  sup_num_of_loops:                       47
% 3.04/0.96  sup_fw_superposition:                   23
% 3.04/0.96  sup_bw_superposition:                   53
% 3.04/0.96  sup_immediate_simplified:               10
% 3.04/0.96  sup_given_eliminated:                   0
% 3.04/0.96  comparisons_done:                       0
% 3.04/0.96  comparisons_avoided:                    3
% 3.04/0.96  
% 3.04/0.96  ------ Simplifications
% 3.04/0.96  
% 3.04/0.96  
% 3.04/0.96  sim_fw_subset_subsumed:                 6
% 3.04/0.96  sim_bw_subset_subsumed:                 3
% 3.04/0.96  sim_fw_subsumed:                        7
% 3.04/0.96  sim_bw_subsumed:                        0
% 3.04/0.96  sim_fw_subsumption_res:                 3
% 3.04/0.96  sim_bw_subsumption_res:                 5
% 3.04/0.96  sim_tautology_del:                      0
% 3.04/0.96  sim_eq_tautology_del:                   2
% 3.04/0.96  sim_eq_res_simp:                        0
% 3.04/0.96  sim_fw_demodulated:                     0
% 3.04/0.96  sim_bw_demodulated:                     26
% 3.04/0.96  sim_light_normalised:                   5
% 3.04/0.96  sim_joinable_taut:                      0
% 3.04/0.96  sim_joinable_simp:                      0
% 3.04/0.96  sim_ac_normalised:                      0
% 3.04/0.96  sim_smt_subsumption:                    0
% 3.04/0.96  
%------------------------------------------------------------------------------
