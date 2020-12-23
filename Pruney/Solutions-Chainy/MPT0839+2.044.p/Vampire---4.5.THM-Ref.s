%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:48 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 136 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  237 ( 473 expanded)
%              Number of equality atoms :   51 (  98 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f976,plain,(
    $false ),
    inference(subsumption_resolution,[],[f975,f70])).

fof(f70,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f975,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f974,f304])).

fof(f304,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f43,f302])).

fof(f302,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f43,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f974,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f972])).

fof(f972,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f56,f953])).

fof(f953,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f952,f305])).

fof(f305,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f259,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f259,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,sK4(X3,X4))
      | X3 = X4
      | r2_hidden(sK4(X3,X4),X3) ) ),
    inference(resolution,[],[f51,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f952,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r2_hidden(sK4(k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK2)) ),
    inference(resolution,[],[f948,f292])).

fof(f292,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f44,f290])).

fof(f290,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f44,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f948,plain,
    ( m1_subset_1(sK4(k1_relat_1(sK2),k1_xboole_0),sK1)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f946,f86])).

fof(f86,plain,(
    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f83,plain,(
    r1_tarski(k1_relat_1(sK2),sK1) ),
    inference(resolution,[],[f80,f42])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f79,f69])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f63,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f946,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0,k1_xboole_0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f316,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f316,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0
      | m1_subset_1(sK4(X0,k1_xboole_0),X1) ) ),
    inference(resolution,[],[f305,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:53:56 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.44  % (14629)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.45  % (14621)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.46  % (14637)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.48  % (14616)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.48  % (14621)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f976,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(subsumption_resolution,[],[f975,f70])).
% 0.18/0.48  fof(f70,plain,(
% 0.18/0.48    v1_relat_1(sK2)),
% 0.18/0.48    inference(resolution,[],[f69,f42])).
% 0.18/0.48  fof(f42,plain,(
% 0.18/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.18/0.48    inference(cnf_transformation,[],[f32])).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f31])).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.18/0.48    inference(flattening,[],[f18])).
% 0.18/0.48  fof(f18,plain,(
% 0.18/0.48    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.18/0.48    inference(ennf_transformation,[],[f16])).
% 0.18/0.48  fof(f16,plain,(
% 0.18/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 0.18/0.48    inference(pure_predicate_removal,[],[f15])).
% 0.18/0.48  fof(f15,negated_conjecture,(
% 0.18/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.18/0.48    inference(negated_conjecture,[],[f14])).
% 0.18/0.48  fof(f14,conjecture,(
% 0.18/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.18/0.48  fof(f69,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.18/0.48    inference(resolution,[],[f59,f60])).
% 0.18/0.48  fof(f60,plain,(
% 0.18/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f8])).
% 0.18/0.48  fof(f8,axiom,(
% 0.18/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.18/0.48  fof(f59,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f28])).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f6])).
% 0.18/0.48  fof(f6,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.18/0.48  fof(f975,plain,(
% 0.18/0.48    ~v1_relat_1(sK2)),
% 0.18/0.48    inference(subsumption_resolution,[],[f974,f304])).
% 0.18/0.48  fof(f304,plain,(
% 0.18/0.48    k1_xboole_0 != k2_relat_1(sK2)),
% 0.18/0.48    inference(superposition,[],[f43,f302])).
% 0.18/0.48  fof(f302,plain,(
% 0.18/0.48    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.18/0.48    inference(resolution,[],[f55,f42])).
% 0.18/0.48  fof(f55,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f26])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f13])).
% 0.18/0.48  fof(f13,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.48  fof(f43,plain,(
% 0.18/0.48    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.18/0.48    inference(cnf_transformation,[],[f32])).
% 0.18/0.48  fof(f974,plain,(
% 0.18/0.48    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f972])).
% 0.18/0.48  fof(f972,plain,(
% 0.18/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.18/0.48    inference(superposition,[],[f56,f953])).
% 0.18/0.48  fof(f953,plain,(
% 0.18/0.48    k1_xboole_0 = k1_relat_1(sK2)),
% 0.18/0.48    inference(subsumption_resolution,[],[f952,f305])).
% 0.18/0.48  fof(f305,plain,(
% 0.18/0.48    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.18/0.48    inference(resolution,[],[f259,f58])).
% 0.18/0.48  fof(f58,plain,(
% 0.18/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.48  fof(f259,plain,(
% 0.18/0.48    ( ! [X4,X3] : (~r1_tarski(X4,sK4(X3,X4)) | X3 = X4 | r2_hidden(sK4(X3,X4),X3)) )),
% 0.18/0.48    inference(resolution,[],[f51,f46])).
% 0.18/0.48  fof(f46,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f22])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.18/0.48    inference(ennf_transformation,[],[f10])).
% 0.18/0.48  fof(f10,axiom,(
% 0.18/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.18/0.48  fof(f51,plain,(
% 0.18/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.18/0.48    inference(cnf_transformation,[],[f39])).
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 0.18/0.48  fof(f38,plain,(
% 0.18/0.48    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f37,plain,(
% 0.18/0.48    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.18/0.48    inference(nnf_transformation,[],[f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.18/0.48    inference(ennf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.18/0.48  fof(f952,plain,(
% 0.18/0.48    k1_xboole_0 = k1_relat_1(sK2) | ~r2_hidden(sK4(k1_relat_1(sK2),k1_xboole_0),k1_relat_1(sK2))),
% 0.18/0.48    inference(resolution,[],[f948,f292])).
% 0.18/0.48  fof(f292,plain,(
% 0.18/0.48    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relat_1(sK2))) )),
% 0.18/0.48    inference(backward_demodulation,[],[f44,f290])).
% 0.18/0.48  fof(f290,plain,(
% 0.18/0.48    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.18/0.48    inference(resolution,[],[f54,f42])).
% 0.18/0.48  fof(f54,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f25])).
% 0.18/0.48  fof(f25,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f12])).
% 0.18/0.48  fof(f12,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.48  fof(f44,plain,(
% 0.18/0.48    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f32])).
% 0.18/0.48  fof(f948,plain,(
% 0.18/0.48    m1_subset_1(sK4(k1_relat_1(sK2),k1_xboole_0),sK1) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.18/0.48    inference(resolution,[],[f946,f86])).
% 0.18/0.48  fof(f86,plain,(
% 0.18/0.48    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.18/0.48    inference(resolution,[],[f83,f64])).
% 0.18/0.48  fof(f64,plain,(
% 0.18/0.48    ( ! [X0,X3] : (~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.18/0.48    inference(equality_resolution,[],[f48])).
% 0.18/0.48  fof(f48,plain,(
% 0.18/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.18/0.48    inference(cnf_transformation,[],[f36])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.48    inference(rectify,[],[f33])).
% 0.18/0.48  fof(f33,plain,(
% 0.18/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.48    inference(nnf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.18/0.48  fof(f83,plain,(
% 0.18/0.48    r1_tarski(k1_relat_1(sK2),sK1)),
% 0.18/0.48    inference(resolution,[],[f80,f42])).
% 0.18/0.48  fof(f80,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relat_1(X0),X1)) )),
% 0.18/0.48    inference(subsumption_resolution,[],[f79,f69])).
% 0.18/0.48  fof(f79,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(resolution,[],[f63,f61])).
% 0.18/0.48  fof(f61,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f41])).
% 0.18/0.48  fof(f41,plain,(
% 0.18/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.18/0.48    inference(nnf_transformation,[],[f29])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.18/0.48    inference(ennf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,axiom,(
% 0.18/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.18/0.48  fof(f63,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f30])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f17])).
% 0.18/0.48  fof(f17,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.18/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.18/0.48  fof(f11,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.48  fof(f946,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK4(X0,k1_xboole_0),X1) | k1_xboole_0 = X0) )),
% 0.18/0.48    inference(resolution,[],[f316,f53])).
% 0.18/0.48  fof(f53,plain,(
% 0.18/0.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.18/0.48    inference(ennf_transformation,[],[f4])).
% 0.18/0.48  fof(f4,axiom,(
% 0.18/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.18/0.48  fof(f316,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0 | m1_subset_1(sK4(X0,k1_xboole_0),X1)) )),
% 0.18/0.48    inference(resolution,[],[f305,f45])).
% 0.18/0.48  fof(f45,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f21])).
% 0.18/0.48  fof(f21,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.18/0.48    inference(flattening,[],[f20])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.18/0.48    inference(ennf_transformation,[],[f5])).
% 0.18/0.48  fof(f5,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.18/0.48  fof(f56,plain,(
% 0.18/0.48    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f40])).
% 0.18/0.48  fof(f40,plain,(
% 0.18/0.48    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(nnf_transformation,[],[f27])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f9])).
% 0.18/0.48  fof(f9,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (14621)------------------------------
% 0.18/0.48  % (14621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (14621)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (14621)Memory used [KB]: 6652
% 0.18/0.48  % (14621)Time elapsed: 0.096 s
% 0.18/0.48  % (14621)------------------------------
% 0.18/0.48  % (14621)------------------------------
% 0.18/0.48  % (14615)Success in time 0.145 s
%------------------------------------------------------------------------------
