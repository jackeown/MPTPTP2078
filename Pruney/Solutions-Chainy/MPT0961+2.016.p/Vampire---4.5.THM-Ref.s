%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 455 expanded)
%              Number of leaves         :   11 (  98 expanded)
%              Depth                    :   21
%              Number of atoms          :  237 (1806 expanded)
%              Number of equality atoms :   88 ( 385 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(subsumption_resolution,[],[f227,f136])).

fof(f136,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f135,f93])).

fof(f93,plain,(
    ! [X0,X1] : sP0(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f86,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X0,X2))
      | sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f135,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f65,f128])).

fof(f128,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f124,f38])).

fof(f38,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f124,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f111,f40])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(resolution,[],[f53,f48])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f65,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2)
      | ~ sP0(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f227,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f217,f38])).

fof(f217,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f189,f210])).

fof(f210,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f209,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f209,plain,(
    sK1 = k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f208,f184])).

fof(f184,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f183,f170])).

fof(f170,plain,(
    sP0(k1_relat_1(sK1),sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f167,f58])).

fof(f167,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    inference(resolution,[],[f166,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f166,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK1)))) ) ),
    inference(resolution,[],[f144,f61])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | ~ r1_tarski(k1_relat_1(sK1),X1)
      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
      | ~ v1_funct_1(sK1) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
        | ~ v1_funct_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f183,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ sP0(k1_relat_1(sK1),sK1,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f180,f168])).

fof(f168,plain,(
    ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f70,f167])).

fof(f70,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f37,f36])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f180,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1)
    | ~ sP0(k1_relat_1(sK1),sK1,k2_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))
    | k1_xboole_0 = k2_relat_1(sK1)
    | ~ sP0(k1_relat_1(sK1),sK1,k2_relat_1(sK1)) ),
    inference(superposition,[],[f56,f169])).

fof(f169,plain,(
    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1) ),
    inference(resolution,[],[f167,f53])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f208,plain,(
    sK1 = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f207,f40])).

fof(f207,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f195,f63])).

fof(f195,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0),sK1)
    | sK1 = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f176,f184])).

fof(f176,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),sK1)
    | sK1 = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f171,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f171,plain,(
    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f167,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f189,plain,(
    ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f168,f184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:02:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (24086)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (24086)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f227,f136])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f135,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X0,k1_xboole_0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f86,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(X0,X2)) | sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(resolution,[],[f58,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(definition_folding,[],[f22,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.52    inference(superposition,[],[f65,f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f124,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f111,f40])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(resolution,[],[f53,f48])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2) | ~sP0(k1_xboole_0,X1,X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f217,f38])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f189,f210])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    k1_xboole_0 = sK1),
% 0.21/0.52    inference(forward_demodulation,[],[f209,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    sK1 = k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f208,f184])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f183,f170])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    sP0(k1_relat_1(sK1),sK1,k2_relat_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f167,f58])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))),
% 0.21/0.52    inference(resolution,[],[f166,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK1))))) )),
% 0.21/0.52    inference(resolution,[],[f144,f61])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.52    inference(resolution,[],[f52,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK1) | ~sP0(k1_relat_1(sK1),sK1,k2_relat_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f180,f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f167])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))),
% 0.21/0.52    inference(subsumption_resolution,[],[f37,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1) | ~sP0(k1_relat_1(sK1),sK1,k2_relat_1(sK1))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    k1_relat_1(sK1) != k1_relat_1(sK1) | v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) | k1_xboole_0 = k2_relat_1(sK1) | ~sP0(k1_relat_1(sK1),sK1,k2_relat_1(sK1))),
% 0.21/0.52    inference(superposition,[],[f56,f169])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k2_relat_1(sK1),sK1)),
% 0.21/0.52    inference(resolution,[],[f167,f53])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    sK1 = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f207,f40])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,sK1) | sK1 = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.52    inference(forward_demodulation,[],[f195,f63])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0),sK1) | sK1 = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f176,f184])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),sK1) | sK1 = k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f171,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.21/0.52    inference(resolution,[],[f167,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f168,f184])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (24086)------------------------------
% 0.21/0.52  % (24086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24086)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (24086)Memory used [KB]: 6268
% 0.21/0.52  % (24086)Time elapsed: 0.101 s
% 0.21/0.52  % (24086)------------------------------
% 0.21/0.52  % (24086)------------------------------
% 0.21/0.52  % (24078)Success in time 0.158 s
%------------------------------------------------------------------------------
