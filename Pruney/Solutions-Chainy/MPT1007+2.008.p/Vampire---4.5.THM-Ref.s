%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:52 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 757 expanded)
%              Number of leaves         :   22 ( 212 expanded)
%              Depth                    :   19
%              Number of atoms          :  308 (2272 expanded)
%              Number of equality atoms :   74 ( 615 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f363,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f73,f92,f298,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f298,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f297,f131])).

fof(f131,plain,(
    ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f58,f128])).

fof(f128,plain,(
    k1_xboole_0 = k1_funct_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f117,f54,f125,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f17])).

% (3070)Refutation not found, incomplete strategy% (3070)------------------------------
% (3070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3070)Termination reason: Refutation not found, incomplete strategy

% (3070)Memory used [KB]: 1791
% (3070)Time elapsed: 0.104 s
% (3070)------------------------------
% (3070)------------------------------
fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f125,plain,(
    ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f117,f54,f58,f116,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f116,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f90,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f56,f89])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f117,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f90,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

% (3075)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f58,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f297,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,sK1)
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(forward_demodulation,[],[f252,f283])).

fof(f283,plain,(
    ! [X0] : k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f282,f65])).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f282,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f281,f61])).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f281,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f241,f205])).

fof(f205,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f204,f126])).

fof(f126,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f117,f125,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f204,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f124,f195])).

fof(f195,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f124,f180])).

fof(f180,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | sK0 = X1 ) ),
    inference(resolution,[],[f120,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f85,f89])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f90,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f124,plain,
    ( r2_hidden(k4_tarski(sK3(sK2),sK4(sK2)),sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f117,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f241,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f176,f205])).

fof(f176,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | k1_xboole_0 = k1_funct_1(sK2,X0) ) ),
    inference(resolution,[],[f151,f78])).

% (3083)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (3085)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (3063)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (3074)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (3062)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (3077)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | k1_xboole_0 = k1_funct_1(sK2,X0) ) ),
    inference(resolution,[],[f104,f117])).

fof(f104,plain,(
    ! [X8] :
      ( ~ v1_relat_1(sK2)
      | k1_xboole_0 = k1_funct_1(sK2,X8)
      | r2_hidden(X8,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f54,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f252,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1)
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    inference(backward_demodulation,[],[f202,f205])).

fof(f202,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f201,f91])).

fof(f91,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f55,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f201,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f200,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | k1_xboole_0 = sK1
      | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | r2_hidden(k1_funct_1(sK2,X0),sK1) ) ),
    inference(resolution,[],[f100,f90])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK2,X2,X0)
      | r2_hidden(k1_funct_1(sK2,X1),X0) ) ),
    inference(resolution,[],[f54,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f92,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f63,f89])).

fof(f63,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f8,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (3072)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.51  % (3064)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (3067)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (3072)Refutation not found, incomplete strategy% (3072)------------------------------
% 0.22/0.52  % (3072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3072)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3072)Memory used [KB]: 10746
% 0.22/0.52  % (3072)Time elapsed: 0.105 s
% 0.22/0.52  % (3072)------------------------------
% 0.22/0.52  % (3072)------------------------------
% 1.16/0.52  % (3056)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.16/0.52  % (3066)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.16/0.53  % (3070)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.16/0.53  % (3061)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.16/0.53  % (3078)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.16/0.53  % (3057)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.16/0.53  % (3065)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.16/0.53  % (3069)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.16/0.53  % (3084)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.16/0.53  % (3071)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.16/0.53  % (3058)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.16/0.54  % (3060)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.16/0.54  % (3067)Refutation found. Thanks to Tanya!
% 1.16/0.54  % SZS status Theorem for theBenchmark
% 1.16/0.54  % (3059)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.16/0.54  % (3076)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.55  % (3082)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (3068)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f363,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f73,f92,f298,f75])).
% 1.39/0.55  fof(f75,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.39/0.55    inference(flattening,[],[f33])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.39/0.55  fof(f298,plain,(
% 1.39/0.55    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f297,f131])).
% 1.39/0.55  fof(f131,plain,(
% 1.39/0.55    ~r2_hidden(k1_xboole_0,sK1)),
% 1.39/0.55    inference(backward_demodulation,[],[f58,f128])).
% 1.39/0.55  fof(f128,plain,(
% 1.39/0.55    k1_xboole_0 = k1_funct_1(sK2,sK0)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f117,f54,f125,f96])).
% 1.39/0.55  fof(f96,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(equality_resolution,[],[f72])).
% 1.39/0.55  fof(f72,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f49])).
% 1.39/0.55  fof(f49,plain,(
% 1.39/0.55    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(nnf_transformation,[],[f32])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f31])).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f17])).
% 1.39/0.55  % (3070)Refutation not found, incomplete strategy% (3070)------------------------------
% 1.39/0.55  % (3070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (3070)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (3070)Memory used [KB]: 1791
% 1.39/0.55  % (3070)Time elapsed: 0.104 s
% 1.39/0.55  % (3070)------------------------------
% 1.39/0.55  % (3070)------------------------------
% 1.39/0.55  fof(f17,axiom,(
% 1.39/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 1.39/0.55  fof(f125,plain,(
% 1.39/0.55    ~r2_hidden(sK0,k1_relat_1(sK2))),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f117,f54,f58,f116,f77])).
% 1.39/0.55  fof(f77,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.39/0.55    inference(flattening,[],[f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.39/0.55    inference(ennf_transformation,[],[f18])).
% 1.39/0.55  fof(f18,axiom,(
% 1.39/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 1.39/0.55  fof(f116,plain,(
% 1.39/0.55    v5_relat_1(sK2,sK1)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f90,f83])).
% 1.39/0.55  fof(f83,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f25])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.39/0.55    inference(pure_predicate_removal,[],[f21])).
% 1.39/0.55  fof(f21,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.39/0.55  fof(f90,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.39/0.55    inference(definition_unfolding,[],[f56,f89])).
% 1.39/0.55  fof(f89,plain,(
% 1.39/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.39/0.55    inference(definition_unfolding,[],[f66,f88])).
% 1.39/0.55  fof(f88,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.39/0.55    inference(definition_unfolding,[],[f74,f79])).
% 1.39/0.55  fof(f79,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.55  fof(f74,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.55  fof(f66,plain,(
% 1.39/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.39/0.55    inference(cnf_transformation,[],[f46])).
% 1.39/0.55  fof(f46,plain,(
% 1.39/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f45])).
% 1.39/0.55  fof(f45,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK2,sK0),sK1) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.39/0.55    inference(flattening,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f24])).
% 1.39/0.55  fof(f24,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.39/0.55    inference(negated_conjecture,[],[f23])).
% 1.39/0.55  fof(f23,conjecture,(
% 1.39/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    v1_funct_1(sK2)),
% 1.39/0.55    inference(cnf_transformation,[],[f46])).
% 1.39/0.55  fof(f117,plain,(
% 1.39/0.55    v1_relat_1(sK2)),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f90,f82])).
% 1.39/0.55  fof(f82,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f20])).
% 1.39/0.55  % (3075)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.55  fof(f20,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f46])).
% 1.39/0.55  fof(f297,plain,(
% 1.39/0.55    ( ! [X0] : (r2_hidden(k1_xboole_0,sK1) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.39/0.55    inference(forward_demodulation,[],[f252,f283])).
% 1.39/0.55  fof(f283,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f282,f65])).
% 1.39/0.55  fof(f65,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.55  fof(f282,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(forward_demodulation,[],[f281,f61])).
% 1.39/0.55  fof(f61,plain,(
% 1.39/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(cnf_transformation,[],[f14])).
% 1.39/0.55  fof(f14,axiom,(
% 1.39/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.39/0.55  fof(f281,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | k1_xboole_0 = k1_funct_1(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(forward_demodulation,[],[f241,f205])).
% 1.39/0.55  fof(f205,plain,(
% 1.39/0.55    k1_xboole_0 = sK2),
% 1.39/0.55    inference(subsumption_resolution,[],[f204,f126])).
% 1.39/0.55  fof(f126,plain,(
% 1.39/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK2)) )),
% 1.39/0.55    inference(unit_resulting_resolution,[],[f117,f125,f80])).
% 1.39/0.55  fof(f80,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f40])).
% 1.39/0.55  fof(f40,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.39/0.55    inference(flattening,[],[f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.39/0.55    inference(ennf_transformation,[],[f12])).
% 1.39/0.55  fof(f12,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 1.39/0.55  fof(f204,plain,(
% 1.39/0.55    r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2) | k1_xboole_0 = sK2),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f203])).
% 1.39/0.55  fof(f203,plain,(
% 1.39/0.55    r2_hidden(k4_tarski(sK0,sK4(sK2)),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.39/0.55    inference(superposition,[],[f124,f195])).
% 1.39/0.55  fof(f195,plain,(
% 1.39/0.55    sK0 = sK3(sK2) | k1_xboole_0 = sK2),
% 1.39/0.55    inference(resolution,[],[f124,f180])).
% 1.39/0.55  fof(f180,plain,(
% 1.39/0.55    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK2) | sK0 = X1) )),
% 1.39/0.55    inference(resolution,[],[f120,f95])).
% 1.39/0.55  fof(f95,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) | X0 = X2) )),
% 1.39/0.55    inference(definition_unfolding,[],[f85,f89])).
% 1.39/0.55  fof(f85,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f53])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.39/0.55    inference(flattening,[],[f52])).
% 1.39/0.55  fof(f52,plain,(
% 1.39/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.39/0.55    inference(nnf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.39/0.55  fof(f120,plain,(
% 1.39/0.55    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.39/0.55    inference(resolution,[],[f90,f76])).
% 1.39/0.55  fof(f76,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f35])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,axiom,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.39/0.55  fof(f124,plain,(
% 1.39/0.55    r2_hidden(k4_tarski(sK3(sK2),sK4(sK2)),sK2) | k1_xboole_0 = sK2),
% 1.39/0.55    inference(resolution,[],[f117,f68])).
% 1.39/0.55  fof(f68,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) | k1_xboole_0 = X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f47])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f29])).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,axiom,(
% 1.39/0.55    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 1.39/0.55  fof(f241,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k1_funct_1(k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 1.39/0.55    inference(backward_demodulation,[],[f176,f205])).
% 1.39/0.55  fof(f176,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | k1_xboole_0 = k1_funct_1(sK2,X0)) )),
% 1.39/0.55    inference(resolution,[],[f151,f78])).
% 1.39/0.55  % (3083)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.55  % (3085)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.55  % (3063)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.55  % (3074)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.55  % (3062)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (3077)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.56  fof(f78,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f38])).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.39/0.56    inference(ennf_transformation,[],[f19])).
% 1.39/0.56  fof(f19,axiom,(
% 1.39/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.39/0.56  fof(f151,plain,(
% 1.39/0.56    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | k1_xboole_0 = k1_funct_1(sK2,X0)) )),
% 1.39/0.56    inference(resolution,[],[f104,f117])).
% 1.39/0.56  fof(f104,plain,(
% 1.39/0.56    ( ! [X8] : (~v1_relat_1(sK2) | k1_xboole_0 = k1_funct_1(sK2,X8) | r2_hidden(X8,k1_relat_1(sK2))) )),
% 1.39/0.56    inference(resolution,[],[f54,f97])).
% 1.39/0.56  fof(f97,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = k1_funct_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.39/0.56    inference(equality_resolution,[],[f71])).
% 1.39/0.56  fof(f71,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f49])).
% 1.39/0.56  fof(f252,plain,(
% 1.39/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),sK1) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) )),
% 1.39/0.56    inference(backward_demodulation,[],[f202,f205])).
% 1.39/0.56  fof(f202,plain,(
% 1.39/0.56    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X0),sK1)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f201,f91])).
% 1.39/0.56  fof(f91,plain,(
% 1.39/0.56    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.39/0.56    inference(definition_unfolding,[],[f55,f89])).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.39/0.56    inference(cnf_transformation,[],[f46])).
% 1.39/0.56  fof(f201,plain,(
% 1.39/0.56    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | r2_hidden(k1_funct_1(sK2,X0),sK1)) )),
% 1.39/0.56    inference(subsumption_resolution,[],[f200,f57])).
% 1.39/0.56  fof(f57,plain,(
% 1.39/0.56    k1_xboole_0 != sK1),
% 1.39/0.56    inference(cnf_transformation,[],[f46])).
% 1.39/0.56  fof(f200,plain,(
% 1.39/0.56    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | r2_hidden(k1_funct_1(sK2,X0),sK1)) )),
% 1.39/0.56    inference(resolution,[],[f100,f90])).
% 1.39/0.56  fof(f100,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~v1_funct_2(sK2,X2,X0) | r2_hidden(k1_funct_1(sK2,X1),X0)) )),
% 1.39/0.56    inference(resolution,[],[f54,f84])).
% 1.39/0.56  fof(f84,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f44])).
% 1.39/0.56  fof(f44,plain,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.39/0.56    inference(flattening,[],[f43])).
% 1.39/0.56  fof(f43,plain,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.39/0.56    inference(ennf_transformation,[],[f22])).
% 1.39/0.56  fof(f22,axiom,(
% 1.39/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.39/0.56  fof(f92,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 1.39/0.56    inference(definition_unfolding,[],[f63,f89])).
% 1.39/0.56  fof(f63,plain,(
% 1.39/0.56    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f6])).
% 1.39/0.56  fof(f6,axiom,(
% 1.39/0.56    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.39/0.56  fof(f73,plain,(
% 1.39/0.56    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f51])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    ! [X0] : m1_subset_1(sK5(X0),X0)),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f8,f50])).
% 1.39/0.56  fof(f50,plain,(
% 1.39/0.56    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK5(X0),X0))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (3067)------------------------------
% 1.39/0.56  % (3067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (3067)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (3067)Memory used [KB]: 6524
% 1.39/0.56  % (3067)Time elapsed: 0.116 s
% 1.39/0.56  % (3067)------------------------------
% 1.39/0.56  % (3067)------------------------------
% 1.39/0.56  % (3055)Success in time 0.189 s
%------------------------------------------------------------------------------
