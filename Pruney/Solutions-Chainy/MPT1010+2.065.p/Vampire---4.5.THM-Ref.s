%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:00 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 172 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   20
%              Number of atoms          :  361 ( 658 expanded)
%              Number of equality atoms :  178 ( 271 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f203,plain,(
    $false ),
    inference(subsumption_resolution,[],[f193,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f193,plain,(
    ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(superposition,[],[f103,f155])).

fof(f155,plain,(
    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(subsumption_resolution,[],[f153,f45])).

fof(f45,plain,(
    sK2 != k1_funct_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK2 != k1_funct_1(sK4,sK3)
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK2 != k1_funct_1(sK4,sK3)
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f153,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK2 = k1_funct_1(sK4,sK3) ),
    inference(resolution,[],[f126,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f64,f79])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f126,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK4,sK3)),k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(resolution,[],[f123,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | r2_hidden(X0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) ) ),
    inference(resolution,[],[f49,f80])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(definition_unfolding,[],[f43,f79])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f123,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK4,sK3)),sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(resolution,[],[f122,f44])).

fof(f44,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) ) ),
    inference(resolution,[],[f121,f80])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) ) ),
    inference(resolution,[],[f119,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f119,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ) ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ) ),
    inference(superposition,[],[f90,f117])).

fof(f117,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(subsumption_resolution,[],[f115,f80])).

fof(f115,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) ),
    inference(superposition,[],[f114,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f114,plain,
    ( sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(subsumption_resolution,[],[f113,f81])).

fof(f81,plain,(
    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f42,f79])).

fof(f42,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f113,plain,
    ( ~ v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) ),
    inference(resolution,[],[f54,f80])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f12])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : ~ r1_tarski(k2_enumset1(X0,X1,X2,X3),X0) ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(resolution,[],[f96,f95])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2,X6,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK5(X0,X1,X2,X3,X4) != X0
              & sK5(X0,X1,X2,X3,X4) != X1
              & sK5(X0,X1,X2,X3,X4) != X2
              & sK5(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
          & ( sK5(X0,X1,X2,X3,X4) = X0
            | sK5(X0,X1,X2,X3,X4) = X1
            | sK5(X0,X1,X2,X3,X4) = X2
            | sK5(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4) != X0
            & sK5(X0,X1,X2,X3,X4) != X1
            & sK5(X0,X1,X2,X3,X4) != X2
            & sK5(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
        & ( sK5(X0,X1,X2,X3,X4) = X0
          | sK5(X0,X1,X2,X3,X4) = X1
          | sK5(X0,X1,X2,X3,X4) = X2
          | sK5(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (28820)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (28831)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (28838)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (28831)Refutation not found, incomplete strategy% (28831)------------------------------
% 0.21/0.51  % (28831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28818)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (28819)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (28831)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 1.24/0.52  % (28831)Memory used [KB]: 1791
% 1.24/0.52  % (28831)Time elapsed: 0.101 s
% 1.24/0.52  % (28831)------------------------------
% 1.24/0.52  % (28831)------------------------------
% 1.24/0.52  % (28830)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.24/0.52  % (28839)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.24/0.53  % (28822)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.53  % (28839)Refutation found. Thanks to Tanya!
% 1.24/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % (28817)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.53  % (28821)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.53  % (28816)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.53  % (28845)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.24/0.53  % (28826)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.53  % (28837)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.54  % (28824)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f203,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(subsumption_resolution,[],[f193,f46])).
% 1.40/0.54  fof(f46,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.54  fof(f193,plain,(
% 1.40/0.54    ~r1_tarski(k1_xboole_0,sK2)),
% 1.40/0.54    inference(superposition,[],[f103,f155])).
% 1.40/0.54  fof(f155,plain,(
% 1.40/0.54    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f153,f45])).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    sK2 != k1_funct_1(sK4,sK3)),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f28])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK2 != k1_funct_1(sK4,sK3) & r2_hidden(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) & v1_funct_2(sK4,sK1,k1_tarski(sK2)) & v1_funct_1(sK4))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f16,plain,(
% 1.40/0.54    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.40/0.54    inference(flattening,[],[f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.40/0.54    inference(ennf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,negated_conjecture,(
% 1.40/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.40/0.54    inference(negated_conjecture,[],[f13])).
% 1.40/0.54  fof(f13,conjecture,(
% 1.40/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.40/0.54  fof(f153,plain,(
% 1.40/0.54    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | sK2 = k1_funct_1(sK4,sK3)),
% 1.40/0.54    inference(resolution,[],[f126,f83])).
% 1.40/0.54  fof(f83,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 1.40/0.54    inference(definition_unfolding,[],[f64,f79])).
% 1.40/0.54  fof(f79,plain,(
% 1.40/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f47,f78])).
% 1.40/0.54  fof(f78,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f48,f51])).
% 1.40/0.54  fof(f51,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.40/0.54  fof(f48,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.54  fof(f47,plain,(
% 1.40/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.54  fof(f64,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.40/0.54    inference(flattening,[],[f33])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 1.40/0.54    inference(nnf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 1.40/0.54  fof(f126,plain,(
% 1.40/0.54    r2_hidden(k4_tarski(sK3,k1_funct_1(sK4,sK3)),k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.40/0.54    inference(resolution,[],[f123,f98])).
% 1.40/0.54  fof(f98,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,sK4) | r2_hidden(X0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) )),
% 1.40/0.54    inference(resolution,[],[f49,f80])).
% 1.40/0.54  fof(f80,plain,(
% 1.40/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.40/0.54    inference(definition_unfolding,[],[f43,f79])).
% 1.40/0.54  fof(f43,plain,(
% 1.40/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f17])).
% 1.40/0.54  fof(f17,plain,(
% 1.40/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.40/0.54  fof(f123,plain,(
% 1.40/0.54    r2_hidden(k4_tarski(sK3,k1_funct_1(sK4,sK3)),sK4) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.40/0.54    inference(resolution,[],[f122,f44])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    r2_hidden(sK3,sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f122,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)) )),
% 1.40/0.54    inference(resolution,[],[f121,f80])).
% 1.40/0.54  fof(f121,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,sK1) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)) )),
% 1.40/0.54    inference(resolution,[],[f119,f52])).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.54    inference(ennf_transformation,[],[f10])).
% 1.40/0.54  fof(f10,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.40/0.54  fof(f119,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_relat_1(sK4) | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) | ~r2_hidden(X0,sK1) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f118,f41])).
% 1.40/0.54  fof(f41,plain,(
% 1.40/0.54    v1_funct_1(sK4)),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f118,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)) )),
% 1.40/0.54    inference(superposition,[],[f90,f117])).
% 1.40/0.54  fof(f117,plain,(
% 1.40/0.54    sK1 = k1_relat_1(sK4) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f115,f80])).
% 1.40/0.54  fof(f115,plain,(
% 1.40/0.54    sK1 = k1_relat_1(sK4) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))))),
% 1.40/0.54    inference(superposition,[],[f114,f53])).
% 1.40/0.54  fof(f53,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f20])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.54    inference(ennf_transformation,[],[f11])).
% 1.40/0.54  fof(f11,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.40/0.54  fof(f114,plain,(
% 1.40/0.54    sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f113,f81])).
% 1.40/0.54  fof(f81,plain,(
% 1.40/0.54    v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.40/0.54    inference(definition_unfolding,[],[f42,f79])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    v1_funct_2(sK4,sK1,k1_tarski(sK2))),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f113,plain,(
% 1.40/0.54    ~v1_funct_2(sK4,sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | sK1 = k1_relset_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2),sK4)),
% 1.40/0.54    inference(resolution,[],[f54,f80])).
% 1.40/0.54  fof(f54,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.40/0.54    inference(cnf_transformation,[],[f30])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.54    inference(nnf_transformation,[],[f22])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.54    inference(flattening,[],[f21])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.54    inference(ennf_transformation,[],[f12])).
% 1.40/0.54  fof(f12,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.40/0.54  fof(f90,plain,(
% 1.40/0.54    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.40/0.54    inference(equality_resolution,[],[f62])).
% 1.40/0.54  fof(f62,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f32])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.40/0.54    inference(flattening,[],[f31])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.40/0.54    inference(nnf_transformation,[],[f24])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.40/0.54    inference(flattening,[],[f23])).
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.40/0.54    inference(ennf_transformation,[],[f8])).
% 1.40/0.54  fof(f8,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.40/0.54  fof(f103,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_enumset1(X0,X1,X2,X3),X0)) )),
% 1.40/0.54    inference(resolution,[],[f99,f50])).
% 1.40/0.54  fof(f50,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f18])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.40/0.54    inference(ennf_transformation,[],[f9])).
% 1.40/0.54  fof(f9,axiom,(
% 1.40/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.40/0.54  fof(f99,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k2_enumset1(X0,X1,X2,X3))) )),
% 1.40/0.54    inference(resolution,[],[f96,f95])).
% 1.40/0.54  fof(f95,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X0,X1] : (~sP0(X0,X1,X2,X6,X4) | r2_hidden(X6,X4)) )),
% 1.40/0.54    inference(equality_resolution,[],[f67])).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f39])).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK5(X0,X1,X2,X3,X4) != X0 & sK5(X0,X1,X2,X3,X4) != X1 & sK5(X0,X1,X2,X3,X4) != X2 & sK5(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sK5(X0,X1,X2,X3,X4) = X0 | sK5(X0,X1,X2,X3,X4) = X1 | sK5(X0,X1,X2,X3,X4) = X2 | sK5(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK5(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.40/0.54  fof(f38,plain,(
% 1.40/0.54    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK5(X0,X1,X2,X3,X4) != X0 & sK5(X0,X1,X2,X3,X4) != X1 & sK5(X0,X1,X2,X3,X4) != X2 & sK5(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sK5(X0,X1,X2,X3,X4) = X0 | sK5(X0,X1,X2,X3,X4) = X1 | sK5(X0,X1,X2,X3,X4) = X2 | sK5(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK5(X0,X1,X2,X3,X4),X4))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.40/0.54    inference(rectify,[],[f36])).
% 1.40/0.54  fof(f36,plain,(
% 1.40/0.54    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 1.40/0.54    inference(flattening,[],[f35])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 1.40/0.54    inference(nnf_transformation,[],[f26])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.40/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.40/0.54  fof(f96,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3))) )),
% 1.40/0.54    inference(equality_resolution,[],[f76])).
% 1.40/0.54  fof(f76,plain,(
% 1.40/0.54    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 1.40/0.54    inference(cnf_transformation,[],[f40])).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.40/0.54    inference(nnf_transformation,[],[f27])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 1.40/0.54    inference(definition_folding,[],[f25,f26])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.40/0.54    inference(ennf_transformation,[],[f6])).
% 1.40/0.54  fof(f6,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (28839)------------------------------
% 1.40/0.54  % (28839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (28839)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (28839)Memory used [KB]: 6396
% 1.40/0.54  % (28839)Time elapsed: 0.066 s
% 1.40/0.54  % (28839)------------------------------
% 1.40/0.54  % (28839)------------------------------
% 1.40/0.54  % (28841)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.54  % (28843)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % (28814)Success in time 0.185 s
%------------------------------------------------------------------------------
