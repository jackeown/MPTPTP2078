%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:47 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 378 expanded)
%              Number of leaves         :   12 (  98 expanded)
%              Depth                    :   20
%              Number of atoms          :  265 (2178 expanded)
%              Number of equality atoms :   75 ( 527 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1079,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1067,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1067,plain,(
    ~ r1_tarski(sK5,sK5) ),
    inference(resolution,[],[f1064,f278])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | ~ r1_tarski(sK5,X0) ) ),
    inference(superposition,[],[f266,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f266,plain,(
    ~ r1_tarski(sK5,k1_xboole_0) ),
    inference(resolution,[],[f263,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f263,plain,(
    ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f194,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f194,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f164,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK5,X0)
      | ~ r1_tarski(X0,sK4) ) ),
    inference(resolution,[],[f163,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f163,plain,(
    ~ r1_tarski(sK5,sK4) ),
    inference(subsumption_resolution,[],[f162,f52])).

fof(f52,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
      | ~ v1_funct_2(sK6,sK3,sK5)
      | ~ v1_funct_1(sK6) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_tarski(sK4,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
        | ~ v1_funct_2(sK6,sK3,sK5)
        | ~ v1_funct_1(sK6) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & r1_tarski(sK4,sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f162,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(sK5,sK4) ),
    inference(subsumption_resolution,[],[f159,f51])).

fof(f51,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f159,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(sK5,sK4) ),
    inference(superposition,[],[f142,f93])).

fof(f93,plain,
    ( sK4 = sK5
    | ~ r1_tarski(sK5,sK4) ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f142,plain,
    ( ~ v1_funct_2(sK6,sK3,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(subsumption_resolution,[],[f55,f50])).

fof(f50,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_2(sK6,sK3,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f1064,plain,(
    sP0(sK3,sK5) ),
    inference(subsumption_resolution,[],[f1049,f1063])).

fof(f1063,plain,(
    k1_xboole_0 != sK4 ),
    inference(subsumption_resolution,[],[f1062,f91])).

fof(f91,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1062,plain,
    ( sP0(k1_xboole_0,sK5)
    | k1_xboole_0 != sK4 ),
    inference(subsumption_resolution,[],[f1061,f91])).

fof(f1061,plain,
    ( sP0(k1_xboole_0,sK4)
    | sP0(k1_xboole_0,sK5)
    | k1_xboole_0 != sK4 ),
    inference(superposition,[],[f1048,f54])).

fof(f54,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f1048,plain,
    ( sP0(sK3,sK4)
    | sP0(sK3,sK5) ),
    inference(trivial_inequality_removal,[],[f1047])).

fof(f1047,plain,
    ( sK3 != sK3
    | sP0(sK3,sK5)
    | sP0(sK3,sK4) ),
    inference(superposition,[],[f1043,f252])).

fof(f252,plain,
    ( sK3 = k1_relat_1(sK6)
    | sP0(sK3,sK4) ),
    inference(forward_demodulation,[],[f251,f116])).

fof(f116,plain,(
    k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(resolution,[],[f52,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f251,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK6)
    | sP0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f100,f114])).

fof(f114,plain,(
    sP1(sK3,sK6,sK4) ),
    inference(resolution,[],[f52,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f34,f33,f32])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f100,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK6)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK6,sK4) ),
    inference(resolution,[],[f51,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f1043,plain,
    ( sK3 != k1_relat_1(sK6)
    | sP0(sK3,sK5) ),
    inference(subsumption_resolution,[],[f1037,f998])).

fof(f998,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(resolution,[],[f991,f64])).

fof(f991,plain,(
    r1_tarski(sK6,k2_zfmisc_1(sK3,sK5)) ),
    inference(resolution,[],[f205,f118])).

fof(f118,plain,(
    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f52,f63])).

fof(f205,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,k2_zfmisc_1(X11,sK4))
      | r1_tarski(X10,k2_zfmisc_1(X11,sK5)) ) ),
    inference(resolution,[],[f97,f83])).

fof(f97,plain,(
    ! [X1] : r1_tarski(k2_zfmisc_1(X1,sK4),k2_zfmisc_1(X1,sK5)) ),
    inference(resolution,[],[f53,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f1037,plain,
    ( sK3 != k1_relat_1(sK6)
    | sP0(sK3,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(backward_demodulation,[],[f160,f1008])).

fof(f1008,plain,(
    k1_relat_1(sK6) = k1_relset_1(sK3,sK5,sK6) ),
    inference(resolution,[],[f998,f73])).

fof(f160,plain,
    ( sP0(sK3,sK5)
    | sK3 != k1_relset_1(sK3,sK5,sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(subsumption_resolution,[],[f157,f80])).

fof(f157,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | sK3 != k1_relset_1(sK3,sK5,sK6)
    | sP0(sK3,sK5)
    | ~ sP1(sK3,sK6,sK5) ),
    inference(resolution,[],[f142,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1049,plain,
    ( sP0(sK3,sK5)
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f1048,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 21:03:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (21263)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.12/0.51  % (21255)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.12/0.52  % (21253)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.21/0.53  % (21245)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.21/0.54  % (21250)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.21/0.54  % (21249)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.21/0.54  % (21260)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.21/0.55  % (21258)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.21/0.55  % (21252)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.21/0.55  % (21247)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.21/0.55  % (21251)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.21/0.55  % (21253)Refutation found. Thanks to Tanya!
% 1.21/0.55  % SZS status Theorem for theBenchmark
% 1.21/0.55  % (21265)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.21/0.55  % (21261)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.21/0.55  % (21254)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.21/0.55  % (21257)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.21/0.56  % (21262)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.21/0.56  % SZS output start Proof for theBenchmark
% 1.21/0.56  fof(f1079,plain,(
% 1.21/0.56    $false),
% 1.21/0.56    inference(subsumption_resolution,[],[f1067,f85])).
% 1.21/0.56  fof(f85,plain,(
% 1.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.21/0.56    inference(equality_resolution,[],[f60])).
% 1.21/0.56  fof(f60,plain,(
% 1.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.21/0.56    inference(cnf_transformation,[],[f39])).
% 1.21/0.56  fof(f39,plain,(
% 1.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.21/0.56    inference(flattening,[],[f38])).
% 1.21/0.56  fof(f38,plain,(
% 1.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.21/0.56    inference(nnf_transformation,[],[f1])).
% 1.21/0.56  fof(f1,axiom,(
% 1.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.21/0.56  fof(f1067,plain,(
% 1.21/0.56    ~r1_tarski(sK5,sK5)),
% 1.21/0.56    inference(resolution,[],[f1064,f278])).
% 1.21/0.56  fof(f278,plain,(
% 1.21/0.56    ( ! [X0,X1] : (~sP0(X1,X0) | ~r1_tarski(sK5,X0)) )),
% 1.21/0.56    inference(superposition,[],[f266,f78])).
% 1.21/0.56  fof(f78,plain,(
% 1.21/0.56    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~sP0(X0,X1)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f49])).
% 1.21/0.56  fof(f49,plain,(
% 1.21/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.21/0.56    inference(nnf_transformation,[],[f32])).
% 1.21/0.56  fof(f32,plain,(
% 1.21/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.21/0.56  fof(f266,plain,(
% 1.21/0.56    ~r1_tarski(sK5,k1_xboole_0)),
% 1.21/0.56    inference(resolution,[],[f263,f64])).
% 1.21/0.56  fof(f64,plain,(
% 1.21/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f40])).
% 1.21/0.56  fof(f40,plain,(
% 1.21/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.21/0.56    inference(nnf_transformation,[],[f9])).
% 1.21/0.56  fof(f9,axiom,(
% 1.21/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.21/0.56  fof(f263,plain,(
% 1.21/0.56    ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 1.21/0.56    inference(resolution,[],[f194,f57])).
% 1.21/0.56  fof(f57,plain,(
% 1.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f3])).
% 1.21/0.56  fof(f3,axiom,(
% 1.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.21/0.56  fof(f194,plain,(
% 1.21/0.56    ( ! [X2] : (~r1_tarski(X2,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(X2))) )),
% 1.21/0.56    inference(resolution,[],[f164,f63])).
% 1.21/0.56  fof(f63,plain,(
% 1.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.21/0.56    inference(cnf_transformation,[],[f40])).
% 1.21/0.56  fof(f164,plain,(
% 1.21/0.56    ( ! [X0] : (~r1_tarski(sK5,X0) | ~r1_tarski(X0,sK4)) )),
% 1.21/0.56    inference(resolution,[],[f163,f83])).
% 1.21/0.56  fof(f83,plain,(
% 1.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f31])).
% 1.21/0.56  fof(f31,plain,(
% 1.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.21/0.56    inference(flattening,[],[f30])).
% 1.21/0.56  fof(f30,plain,(
% 1.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.21/0.56    inference(ennf_transformation,[],[f2])).
% 1.21/0.56  fof(f2,axiom,(
% 1.21/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.21/0.56  fof(f163,plain,(
% 1.21/0.56    ~r1_tarski(sK5,sK4)),
% 1.21/0.56    inference(subsumption_resolution,[],[f162,f52])).
% 1.21/0.56  fof(f52,plain,(
% 1.21/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.21/0.56    inference(cnf_transformation,[],[f37])).
% 1.21/0.56  fof(f37,plain,(
% 1.21/0.56    (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(sK4,sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 1.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f36])).
% 1.21/0.56  fof(f36,plain,(
% 1.21/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(sK4,sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 1.21/0.56    introduced(choice_axiom,[])).
% 1.21/0.56  fof(f20,plain,(
% 1.21/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.21/0.56    inference(flattening,[],[f19])).
% 1.21/0.56  fof(f19,plain,(
% 1.21/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.21/0.56    inference(ennf_transformation,[],[f15])).
% 1.21/0.56  fof(f15,negated_conjecture,(
% 1.21/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.21/0.56    inference(negated_conjecture,[],[f14])).
% 1.21/0.56  fof(f14,conjecture,(
% 1.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 1.21/0.56  fof(f162,plain,(
% 1.21/0.56    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~r1_tarski(sK5,sK4)),
% 1.21/0.56    inference(subsumption_resolution,[],[f159,f51])).
% 1.21/0.56  fof(f51,plain,(
% 1.21/0.56    v1_funct_2(sK6,sK3,sK4)),
% 1.21/0.56    inference(cnf_transformation,[],[f37])).
% 1.21/0.56  fof(f159,plain,(
% 1.21/0.56    ~v1_funct_2(sK6,sK3,sK4) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~r1_tarski(sK5,sK4)),
% 1.21/0.56    inference(superposition,[],[f142,f93])).
% 1.21/0.56  fof(f93,plain,(
% 1.21/0.56    sK4 = sK5 | ~r1_tarski(sK5,sK4)),
% 1.21/0.56    inference(resolution,[],[f53,f62])).
% 1.21/0.56  fof(f62,plain,(
% 1.21/0.56    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f39])).
% 1.21/0.56  fof(f53,plain,(
% 1.21/0.56    r1_tarski(sK4,sK5)),
% 1.21/0.56    inference(cnf_transformation,[],[f37])).
% 1.21/0.56  fof(f142,plain,(
% 1.21/0.56    ~v1_funct_2(sK6,sK3,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 1.21/0.56    inference(subsumption_resolution,[],[f55,f50])).
% 1.21/0.56  fof(f50,plain,(
% 1.21/0.56    v1_funct_1(sK6)),
% 1.21/0.56    inference(cnf_transformation,[],[f37])).
% 1.21/0.56  fof(f55,plain,(
% 1.21/0.56    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)),
% 1.21/0.56    inference(cnf_transformation,[],[f37])).
% 1.21/0.56  fof(f1064,plain,(
% 1.21/0.56    sP0(sK3,sK5)),
% 1.21/0.56    inference(subsumption_resolution,[],[f1049,f1063])).
% 1.21/0.56  fof(f1063,plain,(
% 1.21/0.56    k1_xboole_0 != sK4),
% 1.21/0.56    inference(subsumption_resolution,[],[f1062,f91])).
% 1.21/0.56  fof(f91,plain,(
% 1.21/0.56    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 1.21/0.56    inference(equality_resolution,[],[f79])).
% 1.21/0.56  fof(f79,plain,(
% 1.21/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f49])).
% 1.21/0.56  fof(f1062,plain,(
% 1.21/0.56    sP0(k1_xboole_0,sK5) | k1_xboole_0 != sK4),
% 1.21/0.56    inference(subsumption_resolution,[],[f1061,f91])).
% 1.21/0.56  fof(f1061,plain,(
% 1.21/0.56    sP0(k1_xboole_0,sK4) | sP0(k1_xboole_0,sK5) | k1_xboole_0 != sK4),
% 1.21/0.56    inference(superposition,[],[f1048,f54])).
% 1.21/0.56  fof(f54,plain,(
% 1.21/0.56    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 1.21/0.56    inference(cnf_transformation,[],[f37])).
% 1.21/0.56  fof(f1048,plain,(
% 1.21/0.56    sP0(sK3,sK4) | sP0(sK3,sK5)),
% 1.21/0.56    inference(trivial_inequality_removal,[],[f1047])).
% 1.21/0.56  fof(f1047,plain,(
% 1.21/0.56    sK3 != sK3 | sP0(sK3,sK5) | sP0(sK3,sK4)),
% 1.21/0.56    inference(superposition,[],[f1043,f252])).
% 1.21/0.56  fof(f252,plain,(
% 1.21/0.56    sK3 = k1_relat_1(sK6) | sP0(sK3,sK4)),
% 1.21/0.56    inference(forward_demodulation,[],[f251,f116])).
% 1.21/0.56  fof(f116,plain,(
% 1.21/0.56    k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6)),
% 1.21/0.56    inference(resolution,[],[f52,f73])).
% 1.21/0.56  fof(f73,plain,(
% 1.21/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.21/0.56    inference(cnf_transformation,[],[f25])).
% 1.21/0.56  fof(f25,plain,(
% 1.21/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.56    inference(ennf_transformation,[],[f11])).
% 1.21/0.56  fof(f11,axiom,(
% 1.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.21/0.56  fof(f251,plain,(
% 1.21/0.56    sK3 = k1_relset_1(sK3,sK4,sK6) | sP0(sK3,sK4)),
% 1.21/0.56    inference(subsumption_resolution,[],[f100,f114])).
% 1.21/0.56  fof(f114,plain,(
% 1.21/0.56    sP1(sK3,sK6,sK4)),
% 1.21/0.56    inference(resolution,[],[f52,f80])).
% 1.21/0.56  fof(f80,plain,(
% 1.21/0.56    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.21/0.56    inference(cnf_transformation,[],[f35])).
% 1.21/0.56  fof(f35,plain,(
% 1.21/0.56    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.56    inference(definition_folding,[],[f27,f34,f33,f32])).
% 1.21/0.56  fof(f33,plain,(
% 1.21/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.21/0.56  fof(f34,plain,(
% 1.21/0.56    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.21/0.56  fof(f27,plain,(
% 1.21/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.56    inference(flattening,[],[f26])).
% 1.21/0.56  fof(f26,plain,(
% 1.21/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.56    inference(ennf_transformation,[],[f12])).
% 1.21/0.56  fof(f12,axiom,(
% 1.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.21/0.56  fof(f100,plain,(
% 1.21/0.56    sK3 = k1_relset_1(sK3,sK4,sK6) | sP0(sK3,sK4) | ~sP1(sK3,sK6,sK4)),
% 1.21/0.56    inference(resolution,[],[f51,f76])).
% 1.21/0.56  fof(f76,plain,(
% 1.21/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f48])).
% 1.21/0.56  fof(f48,plain,(
% 1.21/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.21/0.56    inference(rectify,[],[f47])).
% 1.21/0.56  fof(f47,plain,(
% 1.21/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.21/0.56    inference(nnf_transformation,[],[f33])).
% 1.21/0.56  fof(f1043,plain,(
% 1.21/0.56    sK3 != k1_relat_1(sK6) | sP0(sK3,sK5)),
% 1.21/0.56    inference(subsumption_resolution,[],[f1037,f998])).
% 1.21/0.56  fof(f998,plain,(
% 1.21/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 1.21/0.56    inference(resolution,[],[f991,f64])).
% 1.21/0.56  fof(f991,plain,(
% 1.21/0.56    r1_tarski(sK6,k2_zfmisc_1(sK3,sK5))),
% 1.21/0.56    inference(resolution,[],[f205,f118])).
% 1.21/0.56  fof(f118,plain,(
% 1.21/0.56    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))),
% 1.21/0.56    inference(resolution,[],[f52,f63])).
% 1.21/0.56  fof(f205,plain,(
% 1.21/0.56    ( ! [X10,X11] : (~r1_tarski(X10,k2_zfmisc_1(X11,sK4)) | r1_tarski(X10,k2_zfmisc_1(X11,sK5))) )),
% 1.21/0.56    inference(resolution,[],[f97,f83])).
% 1.21/0.56  fof(f97,plain,(
% 1.21/0.56    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK4),k2_zfmisc_1(X1,sK5))) )),
% 1.21/0.56    inference(resolution,[],[f53,f72])).
% 1.21/0.56  fof(f72,plain,(
% 1.21/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f24])).
% 1.21/0.56  fof(f24,plain,(
% 1.21/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.21/0.56    inference(ennf_transformation,[],[f5])).
% 1.21/0.56  fof(f5,axiom,(
% 1.21/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.21/0.56  fof(f1037,plain,(
% 1.21/0.56    sK3 != k1_relat_1(sK6) | sP0(sK3,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 1.21/0.56    inference(backward_demodulation,[],[f160,f1008])).
% 1.21/0.56  fof(f1008,plain,(
% 1.21/0.56    k1_relat_1(sK6) = k1_relset_1(sK3,sK5,sK6)),
% 1.21/0.56    inference(resolution,[],[f998,f73])).
% 1.21/0.56  fof(f160,plain,(
% 1.21/0.56    sP0(sK3,sK5) | sK3 != k1_relset_1(sK3,sK5,sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))),
% 1.21/0.56    inference(subsumption_resolution,[],[f157,f80])).
% 1.21/0.56  fof(f157,plain,(
% 1.21/0.56    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | sK3 != k1_relset_1(sK3,sK5,sK6) | sP0(sK3,sK5) | ~sP1(sK3,sK6,sK5)),
% 1.21/0.56    inference(resolution,[],[f142,f77])).
% 1.21/0.56  fof(f77,plain,(
% 1.21/0.56    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.21/0.56    inference(cnf_transformation,[],[f48])).
% 1.21/0.56  fof(f1049,plain,(
% 1.21/0.56    sP0(sK3,sK5) | k1_xboole_0 = sK4),
% 1.21/0.56    inference(resolution,[],[f1048,f78])).
% 1.21/0.56  % SZS output end Proof for theBenchmark
% 1.21/0.56  % (21253)------------------------------
% 1.21/0.56  % (21253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.56  % (21253)Termination reason: Refutation
% 1.21/0.56  
% 1.21/0.56  % (21253)Memory used [KB]: 2046
% 1.21/0.56  % (21253)Time elapsed: 0.109 s
% 1.21/0.56  % (21253)------------------------------
% 1.21/0.56  % (21253)------------------------------
% 1.21/0.56  % (21246)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.56  % (21244)Success in time 0.191 s
%------------------------------------------------------------------------------
