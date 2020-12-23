%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:43 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 328 expanded)
%              Number of leaves         :   20 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          :  262 ( 805 expanded)
%              Number of equality atoms :   73 ( 290 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f546,plain,(
    $false ),
    inference(subsumption_resolution,[],[f545,f406])).

fof(f406,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f221,f99])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f221,plain,(
    ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))))) ),
    inference(unit_resulting_resolution,[],[f215,f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f84,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f215,plain,(
    ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))) ),
    inference(unit_resulting_resolution,[],[f212,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f212,plain,(
    ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(backward_demodulation,[],[f88,f131])).

fof(f131,plain,(
    ! [X0] : k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f89,f85])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f53,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f88,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f55,f87,f87])).

fof(f55,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f545,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f544,f99])).

fof(f544,plain,(
    ! [X3] : m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) ),
    inference(subsumption_resolution,[],[f543,f121])).

fof(f121,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f59,f89,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f543,plain,(
    ! [X3] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f542,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f542,plain,(
    ! [X3] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f532,f153])).

fof(f153,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f107,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f107,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f56,f71])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f532,plain,(
    ! [X3] :
      ( r2_hidden(sK4(k1_xboole_0,X3,sK3),k1_xboole_0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f101,f502])).

fof(f502,plain,(
    k1_xboole_0 = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f171,f267,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f68,f87,f87])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f267,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f135,f218])).

fof(f218,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f217,f121])).

fof(f217,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f216,f52])).

fof(f216,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f212,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f64,f87,f87])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f135,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f121,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f171,plain,(
    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f121,f120,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f120,plain,(
    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f89,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f101,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n011.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 15:37:42 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.33  ipcrm: permission denied for id (812056577)
% 0.16/0.33  ipcrm: permission denied for id (812187653)
% 0.16/0.33  ipcrm: permission denied for id (812220422)
% 0.16/0.34  ipcrm: permission denied for id (812285960)
% 0.16/0.34  ipcrm: permission denied for id (812449806)
% 0.16/0.35  ipcrm: permission denied for id (812515344)
% 0.16/0.35  ipcrm: permission denied for id (812613653)
% 0.16/0.35  ipcrm: permission denied for id (812679191)
% 0.16/0.36  ipcrm: permission denied for id (812744729)
% 0.16/0.36  ipcrm: permission denied for id (812810267)
% 0.16/0.36  ipcrm: permission denied for id (812843036)
% 0.16/0.36  ipcrm: permission denied for id (812875805)
% 0.16/0.36  ipcrm: permission denied for id (812941344)
% 0.16/0.37  ipcrm: permission denied for id (813039651)
% 0.18/0.37  ipcrm: permission denied for id (813105189)
% 0.18/0.38  ipcrm: permission denied for id (813334572)
% 0.18/0.38  ipcrm: permission denied for id (813367341)
% 0.18/0.38  ipcrm: permission denied for id (813400111)
% 0.18/0.38  ipcrm: permission denied for id (813432880)
% 0.18/0.39  ipcrm: permission denied for id (813498420)
% 0.18/0.39  ipcrm: permission denied for id (813596727)
% 0.18/0.40  ipcrm: permission denied for id (813629496)
% 0.18/0.40  ipcrm: permission denied for id (813727803)
% 0.18/0.40  ipcrm: permission denied for id (813760572)
% 0.18/0.40  ipcrm: permission denied for id (813793341)
% 0.18/0.40  ipcrm: permission denied for id (813826110)
% 0.18/0.40  ipcrm: permission denied for id (813858879)
% 0.18/0.41  ipcrm: permission denied for id (813891648)
% 0.18/0.41  ipcrm: permission denied for id (813924417)
% 0.18/0.41  ipcrm: permission denied for id (814022724)
% 0.18/0.41  ipcrm: permission denied for id (814055494)
% 0.18/0.41  ipcrm: permission denied for id (814088263)
% 0.18/0.42  ipcrm: permission denied for id (814153801)
% 0.18/0.42  ipcrm: permission denied for id (814186570)
% 0.18/0.42  ipcrm: permission denied for id (814317645)
% 0.18/0.43  ipcrm: permission denied for id (814481490)
% 0.18/0.43  ipcrm: permission denied for id (814514260)
% 0.18/0.43  ipcrm: permission denied for id (814547029)
% 0.18/0.43  ipcrm: permission denied for id (814579798)
% 0.18/0.44  ipcrm: permission denied for id (814612568)
% 0.18/0.44  ipcrm: permission denied for id (814710877)
% 0.18/0.44  ipcrm: permission denied for id (814743646)
% 0.18/0.45  ipcrm: permission denied for id (814841953)
% 0.18/0.45  ipcrm: permission denied for id (814940262)
% 0.18/0.46  ipcrm: permission denied for id (814973032)
% 0.18/0.46  ipcrm: permission denied for id (815005801)
% 0.18/0.47  ipcrm: permission denied for id (815202416)
% 0.18/0.47  ipcrm: permission denied for id (815300723)
% 0.18/0.47  ipcrm: permission denied for id (815333492)
% 0.18/0.47  ipcrm: permission denied for id (815366262)
% 0.18/0.48  ipcrm: permission denied for id (815562878)
% 0.83/0.63  % (11205)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.83/0.64  % (11232)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.83/0.64  % (11208)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.83/0.64  % (11220)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.83/0.64  % (11224)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.83/0.64  % (11216)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.83/0.65  % (11215)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.83/0.65  % (11232)Refutation not found, incomplete strategy% (11232)------------------------------
% 0.83/0.65  % (11232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.83/0.65  % (11213)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.83/0.65  % (11213)Refutation not found, incomplete strategy% (11213)------------------------------
% 0.83/0.65  % (11213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.66  % (11223)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.66  % (11213)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.66  
% 1.42/0.66  % (11213)Memory used [KB]: 10746
% 1.42/0.66  % (11213)Time elapsed: 0.122 s
% 1.42/0.66  % (11213)------------------------------
% 1.42/0.66  % (11213)------------------------------
% 1.42/0.66  % (11219)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.66  % (11232)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.66  
% 1.42/0.66  % (11232)Memory used [KB]: 1663
% 1.42/0.66  % (11232)Time elapsed: 0.129 s
% 1.42/0.66  % (11232)------------------------------
% 1.42/0.66  % (11232)------------------------------
% 1.42/0.66  % (11203)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.66  % (11226)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.66  % (11204)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.42/0.66  % (11204)Refutation not found, incomplete strategy% (11204)------------------------------
% 1.42/0.66  % (11204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.66  % (11204)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.66  
% 1.42/0.66  % (11204)Memory used [KB]: 1663
% 1.42/0.66  % (11204)Time elapsed: 0.127 s
% 1.42/0.66  % (11204)------------------------------
% 1.42/0.66  % (11204)------------------------------
% 1.42/0.66  % (11209)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.66  % (11228)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.66  % (11206)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.42/0.66  % (11222)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.67  % (11207)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.42/0.67  % (11210)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.67  % (11212)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.67  % (11221)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.59/0.67  % (11219)Refutation not found, incomplete strategy% (11219)------------------------------
% 1.59/0.67  % (11219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.67  % (11219)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.67  
% 1.59/0.67  % (11219)Memory used [KB]: 10618
% 1.59/0.67  % (11219)Time elapsed: 0.141 s
% 1.59/0.67  % (11219)------------------------------
% 1.59/0.67  % (11219)------------------------------
% 1.59/0.68  % (11211)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.59/0.68  % (11225)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.59/0.68  % (11214)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.59/0.68  % (11218)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.59/0.68  % (11229)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.59/0.68  % (11227)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.59/0.69  % (11227)Refutation not found, incomplete strategy% (11227)------------------------------
% 1.59/0.69  % (11227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.69  % (11227)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.69  
% 1.59/0.69  % (11227)Memory used [KB]: 10746
% 1.59/0.69  % (11227)Time elapsed: 0.135 s
% 1.59/0.69  % (11227)------------------------------
% 1.59/0.69  % (11227)------------------------------
% 1.59/0.69  % (11217)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.59/0.69  % (11217)Refutation not found, incomplete strategy% (11217)------------------------------
% 1.59/0.69  % (11217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.69  % (11217)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.69  
% 1.59/0.69  % (11217)Memory used [KB]: 1791
% 1.59/0.69  % (11217)Time elapsed: 0.153 s
% 1.59/0.69  % (11217)------------------------------
% 1.59/0.69  % (11217)------------------------------
% 1.59/0.69  % (11231)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.59/0.69  % (11230)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.69  % (11230)Refutation not found, incomplete strategy% (11230)------------------------------
% 1.59/0.69  % (11230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.69  % (11230)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.69  
% 1.59/0.69  % (11230)Memory used [KB]: 6268
% 1.59/0.69  % (11230)Time elapsed: 0.165 s
% 1.59/0.69  % (11230)------------------------------
% 1.59/0.69  % (11230)------------------------------
% 1.59/0.69  % (11231)Refutation not found, incomplete strategy% (11231)------------------------------
% 1.59/0.69  % (11231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.69  % (11231)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.69  
% 1.59/0.69  % (11231)Memory used [KB]: 10746
% 1.59/0.69  % (11231)Time elapsed: 0.164 s
% 1.59/0.69  % (11231)------------------------------
% 1.59/0.69  % (11231)------------------------------
% 1.59/0.69  % (11207)Refutation found. Thanks to Tanya!
% 1.59/0.69  % SZS status Theorem for theBenchmark
% 1.59/0.69  % SZS output start Proof for theBenchmark
% 1.59/0.69  fof(f546,plain,(
% 1.59/0.69    $false),
% 1.59/0.69    inference(subsumption_resolution,[],[f545,f406])).
% 1.59/0.69  fof(f406,plain,(
% 1.59/0.69    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.59/0.69    inference(superposition,[],[f221,f99])).
% 1.59/0.69  fof(f99,plain,(
% 1.59/0.69    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.59/0.69    inference(equality_resolution,[],[f74])).
% 1.59/0.69  fof(f74,plain,(
% 1.59/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.59/0.69    inference(cnf_transformation,[],[f49])).
% 1.59/0.69  fof(f49,plain,(
% 1.59/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.59/0.69    inference(flattening,[],[f48])).
% 1.59/0.69  fof(f48,plain,(
% 1.59/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.59/0.69    inference(nnf_transformation,[],[f6])).
% 1.59/0.69  fof(f6,axiom,(
% 1.59/0.69    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.59/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.59/0.69  fof(f221,plain,(
% 1.59/0.69    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))))) )),
% 1.59/0.69    inference(unit_resulting_resolution,[],[f215,f133])).
% 1.59/0.69  fof(f133,plain,(
% 1.59/0.69    ( ! [X2,X0,X3,X1] : (m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.59/0.69    inference(duplicate_literal_removal,[],[f132])).
% 1.59/0.69  fof(f132,plain,(
% 1.59/0.69    ( ! [X2,X0,X3,X1] : (m1_subset_1(k9_relat_1(X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.59/0.69    inference(superposition,[],[f84,f85])).
% 1.59/0.69  fof(f85,plain,(
% 1.59/0.69    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.59/0.69    inference(cnf_transformation,[],[f39])).
% 1.59/0.69  fof(f39,plain,(
% 1.59/0.69    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.69    inference(ennf_transformation,[],[f18])).
% 1.59/0.69  fof(f18,axiom,(
% 1.59/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.59/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.59/0.69  fof(f84,plain,(
% 1.59/0.69    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.59/0.69    inference(cnf_transformation,[],[f38])).
% 1.59/0.69  fof(f38,plain,(
% 1.59/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.69    inference(ennf_transformation,[],[f17])).
% 1.59/0.69  fof(f17,axiom,(
% 1.59/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.59/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.59/0.69  fof(f215,plain,(
% 1.59/0.69    ~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))))),
% 1.59/0.69    inference(unit_resulting_resolution,[],[f212,f71])).
% 1.59/0.69  fof(f71,plain,(
% 1.59/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.59/0.69    inference(cnf_transformation,[],[f47])).
% 1.59/0.69  fof(f47,plain,(
% 1.59/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.59/0.69    inference(nnf_transformation,[],[f8])).
% 1.59/0.69  fof(f8,axiom,(
% 1.59/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.69  fof(f212,plain,(
% 1.59/0.69    ~r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.59/0.69    inference(backward_demodulation,[],[f88,f131])).
% 1.59/0.69  fof(f131,plain,(
% 1.59/0.69    ( ! [X0] : (k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.59/0.69    inference(unit_resulting_resolution,[],[f89,f85])).
% 1.59/0.69  fof(f89,plain,(
% 1.59/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.59/0.69    inference(definition_unfolding,[],[f53,f87])).
% 1.59/0.69  fof(f87,plain,(
% 1.59/0.69    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.59/0.69    inference(definition_unfolding,[],[f57,f86])).
% 1.59/0.69  fof(f86,plain,(
% 1.59/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.59/0.69    inference(definition_unfolding,[],[f60,f77])).
% 1.59/0.69  fof(f77,plain,(
% 1.59/0.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.69    inference(cnf_transformation,[],[f4])).
% 1.59/0.69  fof(f4,axiom,(
% 1.59/0.69    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.69  fof(f60,plain,(
% 1.59/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.59/0.69    inference(cnf_transformation,[],[f3])).
% 1.59/0.69  fof(f3,axiom,(
% 1.59/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.59/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.69  fof(f57,plain,(
% 1.59/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/0.69    inference(cnf_transformation,[],[f2])).
% 1.59/0.69  fof(f2,axiom,(
% 1.59/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.59/0.69  fof(f53,plain,(
% 1.59/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.59/0.69    inference(cnf_transformation,[],[f41])).
% 1.59/0.69  fof(f41,plain,(
% 1.59/0.69    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 1.59/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f40])).
% 1.59/0.69  fof(f40,plain,(
% 1.59/0.69    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 1.59/0.69    introduced(choice_axiom,[])).
% 1.59/0.69  fof(f26,plain,(
% 1.59/0.69    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.59/0.69    inference(flattening,[],[f25])).
% 1.59/0.69  fof(f25,plain,(
% 1.59/0.69    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.59/0.69    inference(ennf_transformation,[],[f22])).
% 1.59/0.69  fof(f22,plain,(
% 1.59/0.69    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.59/0.69    inference(pure_predicate_removal,[],[f21])).
% 1.59/0.69  fof(f21,negated_conjecture,(
% 1.59/0.69    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.59/0.69    inference(negated_conjecture,[],[f20])).
% 1.59/0.69  fof(f20,conjecture,(
% 1.59/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.59/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.59/0.69  fof(f88,plain,(
% 1.59/0.69    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.59/0.69    inference(definition_unfolding,[],[f55,f87,f87])).
% 1.59/0.69  fof(f55,plain,(
% 1.59/0.69    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.59/0.69    inference(cnf_transformation,[],[f41])).
% 1.59/0.69  fof(f545,plain,(
% 1.59/0.69    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.59/0.69    inference(forward_demodulation,[],[f544,f99])).
% 1.59/0.70  fof(f544,plain,(
% 1.59/0.70    ( ! [X3] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))) )),
% 1.59/0.70    inference(subsumption_resolution,[],[f543,f121])).
% 1.59/0.70  fof(f121,plain,(
% 1.59/0.70    v1_relat_1(sK3)),
% 1.59/0.70    inference(unit_resulting_resolution,[],[f59,f89,f58])).
% 1.59/0.70  fof(f58,plain,(
% 1.59/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.59/0.70    inference(cnf_transformation,[],[f27])).
% 1.59/0.70  fof(f27,plain,(
% 1.59/0.70    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.59/0.70    inference(ennf_transformation,[],[f10])).
% 1.59/0.70  fof(f10,axiom,(
% 1.59/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.59/0.70  fof(f59,plain,(
% 1.59/0.70    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.59/0.70    inference(cnf_transformation,[],[f12])).
% 1.59/0.70  fof(f12,axiom,(
% 1.59/0.70    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.59/0.70  fof(f543,plain,(
% 1.59/0.70    ( ! [X3] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) | ~v1_relat_1(sK3)) )),
% 1.59/0.70    inference(subsumption_resolution,[],[f542,f52])).
% 1.59/0.70  fof(f52,plain,(
% 1.59/0.70    v1_funct_1(sK3)),
% 1.59/0.70    inference(cnf_transformation,[],[f41])).
% 1.59/0.70  fof(f542,plain,(
% 1.59/0.70    ( ! [X3] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.59/0.70    inference(subsumption_resolution,[],[f532,f153])).
% 1.59/0.70  fof(f153,plain,(
% 1.59/0.70    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.59/0.70    inference(unit_resulting_resolution,[],[f107,f76])).
% 1.59/0.70  fof(f76,plain,(
% 1.59/0.70    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.59/0.70    inference(cnf_transformation,[],[f32])).
% 1.59/0.70  fof(f32,plain,(
% 1.59/0.70    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.59/0.70    inference(ennf_transformation,[],[f15])).
% 1.59/0.70  fof(f15,axiom,(
% 1.59/0.70    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.59/0.70  fof(f107,plain,(
% 1.59/0.70    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.70    inference(unit_resulting_resolution,[],[f56,f71])).
% 1.59/0.70  fof(f56,plain,(
% 1.59/0.70    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.59/0.70    inference(cnf_transformation,[],[f7])).
% 1.59/0.70  fof(f7,axiom,(
% 1.59/0.70    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.59/0.70  fof(f532,plain,(
% 1.59/0.70    ( ! [X3] : (r2_hidden(sK4(k1_xboole_0,X3,sK3),k1_xboole_0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.59/0.70    inference(superposition,[],[f101,f502])).
% 1.59/0.70  fof(f502,plain,(
% 1.59/0.70    k1_xboole_0 = k1_relat_1(sK3)),
% 1.59/0.70    inference(unit_resulting_resolution,[],[f171,f267,f93])).
% 1.59/0.70  fof(f93,plain,(
% 1.59/0.70    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.59/0.70    inference(definition_unfolding,[],[f68,f87,f87])).
% 1.59/0.70  fof(f68,plain,(
% 1.59/0.70    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.59/0.70    inference(cnf_transformation,[],[f46])).
% 1.59/0.70  fof(f46,plain,(
% 1.59/0.70    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.59/0.70    inference(flattening,[],[f45])).
% 1.59/0.70  fof(f45,plain,(
% 1.59/0.70    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.59/0.70    inference(nnf_transformation,[],[f5])).
% 1.59/0.70  fof(f5,axiom,(
% 1.59/0.70    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.59/0.70  fof(f267,plain,(
% 1.59/0.70    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3)),
% 1.59/0.70    inference(unit_resulting_resolution,[],[f135,f218])).
% 1.59/0.70  fof(f218,plain,(
% 1.59/0.70    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 1.59/0.70    inference(subsumption_resolution,[],[f217,f121])).
% 1.59/0.70  fof(f217,plain,(
% 1.59/0.70    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.59/0.70    inference(subsumption_resolution,[],[f216,f52])).
% 1.59/0.70  fof(f216,plain,(
% 1.59/0.70    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.59/0.70    inference(superposition,[],[f212,f90])).
% 1.59/0.70  fof(f90,plain,(
% 1.59/0.70    ( ! [X0,X1] : (k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.59/0.70    inference(definition_unfolding,[],[f64,f87,f87])).
% 1.59/0.70  fof(f64,plain,(
% 1.59/0.70    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.59/0.70    inference(cnf_transformation,[],[f31])).
% 1.59/0.70  fof(f31,plain,(
% 1.59/0.70    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.59/0.70    inference(flattening,[],[f30])).
% 1.59/0.70  fof(f30,plain,(
% 1.59/0.70    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.59/0.70    inference(ennf_transformation,[],[f14])).
% 1.59/0.70  fof(f14,axiom,(
% 1.59/0.70    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.59/0.70  fof(f135,plain,(
% 1.59/0.70    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) )),
% 1.59/0.70    inference(unit_resulting_resolution,[],[f121,f61])).
% 1.59/0.70  fof(f61,plain,(
% 1.59/0.70    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.59/0.70    inference(cnf_transformation,[],[f28])).
% 1.59/0.70  fof(f28,plain,(
% 1.59/0.70    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.59/0.70    inference(ennf_transformation,[],[f13])).
% 1.59/0.70  fof(f13,axiom,(
% 1.59/0.70    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.59/0.70  fof(f171,plain,(
% 1.59/0.70    r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.59/0.70    inference(unit_resulting_resolution,[],[f121,f120,f62])).
% 1.59/0.70  fof(f62,plain,(
% 1.59/0.70    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.59/0.70    inference(cnf_transformation,[],[f42])).
% 1.59/0.70  fof(f42,plain,(
% 1.59/0.70    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.59/0.70    inference(nnf_transformation,[],[f29])).
% 1.59/0.70  fof(f29,plain,(
% 1.59/0.70    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.70    inference(ennf_transformation,[],[f11])).
% 1.59/0.70  fof(f11,axiom,(
% 1.59/0.70    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.59/0.70  fof(f120,plain,(
% 1.59/0.70    v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.59/0.70    inference(unit_resulting_resolution,[],[f89,f78])).
% 1.59/0.70  fof(f78,plain,(
% 1.59/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.59/0.70    inference(cnf_transformation,[],[f33])).
% 1.59/0.70  fof(f33,plain,(
% 1.59/0.70    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.59/0.70    inference(ennf_transformation,[],[f24])).
% 1.59/0.70  fof(f24,plain,(
% 1.59/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.59/0.70    inference(pure_predicate_removal,[],[f16])).
% 1.59/0.70  fof(f16,axiom,(
% 1.59/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.59/0.70  fof(f101,plain,(
% 1.59/0.70    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.59/0.70    inference(equality_resolution,[],[f81])).
% 1.59/0.70  fof(f81,plain,(
% 1.59/0.70    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.59/0.70    inference(cnf_transformation,[],[f51])).
% 1.59/0.70  fof(f51,plain,(
% 1.59/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.59/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f50])).
% 1.59/0.70  fof(f50,plain,(
% 1.59/0.70    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 1.59/0.70    introduced(choice_axiom,[])).
% 1.59/0.70  fof(f35,plain,(
% 1.59/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.59/0.70    inference(flattening,[],[f34])).
% 1.59/0.70  fof(f34,plain,(
% 1.59/0.70    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.59/0.70    inference(ennf_transformation,[],[f23])).
% 1.59/0.70  fof(f23,plain,(
% 1.59/0.70    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))))),
% 1.59/0.70    inference(pure_predicate_removal,[],[f19])).
% 1.59/0.70  fof(f19,axiom,(
% 1.59/0.70    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.59/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 1.59/0.70  % SZS output end Proof for theBenchmark
% 1.59/0.70  % (11207)------------------------------
% 1.59/0.70  % (11207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.70  % (11207)Termination reason: Refutation
% 1.59/0.70  
% 1.59/0.70  % (11207)Memory used [KB]: 2046
% 1.59/0.70  % (11207)Time elapsed: 0.166 s
% 1.59/0.70  % (11207)------------------------------
% 1.59/0.70  % (11207)------------------------------
% 1.59/0.70  % (11012)Success in time 0.376 s
%------------------------------------------------------------------------------
