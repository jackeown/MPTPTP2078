%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:21 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 427 expanded)
%              Number of leaves         :   28 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  404 (1630 expanded)
%              Number of equality atoms :  123 ( 812 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f769,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f520,f527,f609,f629,f630,f652,f695,f697,f762])).

fof(f762,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_29
    | ~ spl3_30
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | ~ spl3_7
    | spl3_8
    | ~ spl3_29
    | ~ spl3_30
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f760,f735])).

fof(f735,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f608,f719])).

fof(f719,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_29 ),
    inference(resolution,[],[f583,f121])).

fof(f121,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f73,f94])).

fof(f94,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f583,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f581])).

fof(f581,plain,
    ( spl3_29
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f608,plain,
    ( ! [X0] : v4_relat_1(sK2,X0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f607])).

fof(f607,plain,
    ( spl3_32
  <=> ! [X0] : v4_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f760,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_7
    | spl3_8
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f712,f713])).

fof(f713,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_30 ),
    inference(resolution,[],[f595,f121])).

fof(f595,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl3_30
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f712,plain,
    ( ~ v4_relat_1(sK1,k1_xboole_0)
    | ~ spl3_7
    | spl3_8 ),
    inference(forward_demodulation,[],[f260,f257])).

fof(f257,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl3_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f260,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl3_8
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f697,plain,
    ( spl3_29
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f696,f255,f581])).

fof(f696,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f674,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f674,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f445,f257])).

fof(f445,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK0)) ),
    inference(subsumption_resolution,[],[f440,f97])).

fof(f97,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f81,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    & sK0 = k2_relset_1(sK0,sK0,sK2)
    & sK0 = k2_relset_1(sK0,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
            & k2_relset_1(X0,X0,X2) = X0
            & k2_relset_1(X0,X0,X1) = X0
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1))
          & sK0 = k2_relset_1(sK0,sK0,X2)
          & sK0 = k2_relset_1(sK0,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1))
        & sK0 = k2_relset_1(sK0,sK0,X2)
        & sK0 = k2_relset_1(sK0,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
   => ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
      & sK0 = k2_relset_1(sK0,sK0,sK2)
      & sK0 = k2_relset_1(sK0,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f440,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK0))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f59,f414])).

fof(f414,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f409,f54])).

fof(f409,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f82,f56])).

fof(f56,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f695,plain,
    ( spl3_30
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f694,f255,f593])).

fof(f694,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f673,f88])).

fof(f673,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f435,f257])).

fof(f435,plain,(
    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) ),
    inference(subsumption_resolution,[],[f430,f96])).

fof(f96,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f430,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f59,f413])).

fof(f413,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f408,f53])).

fof(f408,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f82,f55])).

fof(f55,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f652,plain,
    ( spl3_22
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f651,f418,f513])).

fof(f513,plain,
    ( spl3_22
  <=> m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f418,plain,
    ( spl3_16
  <=> m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f651,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f650,f54])).

fof(f650,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f644,f53])).

fof(f644,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_16 ),
    inference(superposition,[],[f419,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f419,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f418])).

fof(f630,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f319,f259,f255])).

fof(f319,plain,
    ( v4_relat_1(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,
    ( v4_relat_1(sK1,sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f240,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f240,plain,(
    v4_relat_1(sK1,k1_relat_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f238,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f238,plain,
    ( v4_relat_1(sK1,k1_relat_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f212,f116])).

fof(f116,plain,(
    ! [X2] :
      ( v4_relat_1(X2,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f68,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f212,plain,(
    ! [X0] :
      ( ~ v4_relat_1(k2_zfmisc_1(sK0,sK0),X0)
      | v4_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f208,f65])).

fof(f208,plain,(
    ! [X0] :
      ( v4_relat_1(sK1,X0)
      | ~ v4_relat_1(k2_zfmisc_1(sK0,sK0),X0)
      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) ) ),
    inference(resolution,[],[f70,f53])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | v4_relat_1(X2,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

fof(f629,plain,
    ( ~ spl3_8
    | spl3_23 ),
    inference(avatar_split_clause,[],[f543,f517,f259])).

fof(f517,plain,
    ( spl3_23
  <=> sK0 = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f543,plain,
    ( ~ v4_relat_1(sK1,sK0)
    | spl3_23 ),
    inference(subsumption_resolution,[],[f542,f96])).

fof(f542,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | spl3_23 ),
    inference(subsumption_resolution,[],[f541,f413])).

fof(f541,plain,
    ( sK0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | spl3_23 ),
    inference(superposition,[],[f540,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f66,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f540,plain,
    ( sK0 != k9_relat_1(sK1,sK0)
    | spl3_23 ),
    inference(forward_demodulation,[],[f539,f414])).

fof(f539,plain,
    ( sK0 != k9_relat_1(sK1,k2_relat_1(sK2))
    | spl3_23 ),
    inference(subsumption_resolution,[],[f538,f97])).

fof(f538,plain,
    ( sK0 != k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl3_23 ),
    inference(subsumption_resolution,[],[f536,f96])).

fof(f536,plain,
    ( sK0 != k9_relat_1(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | spl3_23 ),
    inference(superposition,[],[f519,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f519,plain,
    ( sK0 != k2_relat_1(k5_relat_1(sK2,sK1))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f517])).

fof(f609,plain,
    ( spl3_32
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f605,f255,f607])).

fof(f605,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK0
      | v4_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f437,f97])).

fof(f437,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK0
      | ~ v1_relat_1(sK2)
      | v4_relat_1(sK2,X0) ) ),
    inference(superposition,[],[f178,f414])).

fof(f178,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k2_relat_1(X3)
      | ~ v1_relat_1(X3)
      | v4_relat_1(X3,X4) ) ),
    inference(subsumption_resolution,[],[f174,f94])).

fof(f174,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_xboole_0,X4)
      | v4_relat_1(X3,X4)
      | ~ v1_relat_1(X3)
      | k1_xboole_0 != k2_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k1_xboole_0,X4)
      | v4_relat_1(X3,X4)
      | ~ v1_relat_1(X3)
      | k1_xboole_0 != k2_relat_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f68,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f527,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl3_16 ),
    inference(subsumption_resolution,[],[f525,f54])).

fof(f525,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_16 ),
    inference(subsumption_resolution,[],[f522,f53])).

fof(f522,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_16 ),
    inference(resolution,[],[f420,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f420,plain,
    ( ~ m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f418])).

fof(f520,plain,
    ( ~ spl3_22
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f511,f517,f513])).

fof(f511,plain,
    ( sK0 != k2_relat_1(k5_relat_1(sK2,sK1))
    | ~ m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f456,f82])).

fof(f456,plain,(
    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f455,f54])).

fof(f455,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f454,f53])).

fof(f454,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f57,f84])).

fof(f57,plain,(
    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:57:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (23191)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.46  % (23202)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (23190)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (23186)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (23193)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (23187)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (23185)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (23200)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (23201)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (23194)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.23/0.52  % (23183)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.52  % (23203)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.23/0.52  % (23206)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.23/0.52  % (23192)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.23/0.52  % (23195)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.23/0.53  % (23204)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.23/0.53  % (23186)Refutation found. Thanks to Tanya!
% 1.23/0.53  % SZS status Theorem for theBenchmark
% 1.23/0.53  % SZS output start Proof for theBenchmark
% 1.23/0.53  fof(f769,plain,(
% 1.23/0.53    $false),
% 1.23/0.53    inference(avatar_sat_refutation,[],[f520,f527,f609,f629,f630,f652,f695,f697,f762])).
% 1.23/0.53  fof(f762,plain,(
% 1.23/0.53    ~spl3_7 | spl3_8 | ~spl3_29 | ~spl3_30 | ~spl3_32),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f761])).
% 1.23/0.53  fof(f761,plain,(
% 1.23/0.53    $false | (~spl3_7 | spl3_8 | ~spl3_29 | ~spl3_30 | ~spl3_32)),
% 1.23/0.53    inference(subsumption_resolution,[],[f760,f735])).
% 1.23/0.53  fof(f735,plain,(
% 1.23/0.53    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | (~spl3_29 | ~spl3_32)),
% 1.23/0.53    inference(backward_demodulation,[],[f608,f719])).
% 1.23/0.53  fof(f719,plain,(
% 1.23/0.53    k1_xboole_0 = sK2 | ~spl3_29),
% 1.23/0.53    inference(resolution,[],[f583,f121])).
% 1.23/0.53  fof(f121,plain,(
% 1.23/0.53    ( ! [X2] : (~r1_tarski(X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 1.23/0.53    inference(resolution,[],[f73,f94])).
% 1.23/0.53  fof(f94,plain,(
% 1.23/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.23/0.53    inference(resolution,[],[f74,f58])).
% 1.23/0.53  fof(f58,plain,(
% 1.23/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f3])).
% 1.23/0.53  fof(f3,axiom,(
% 1.23/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.23/0.53  fof(f74,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f50])).
% 1.23/0.53  fof(f50,plain,(
% 1.23/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.23/0.53    inference(nnf_transformation,[],[f4])).
% 1.23/0.53  fof(f4,axiom,(
% 1.23/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.23/0.53  fof(f73,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f49])).
% 1.23/0.53  fof(f49,plain,(
% 1.23/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.53    inference(flattening,[],[f48])).
% 1.23/0.53  fof(f48,plain,(
% 1.23/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.53    inference(nnf_transformation,[],[f1])).
% 1.23/0.53  fof(f1,axiom,(
% 1.23/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.23/0.53  fof(f583,plain,(
% 1.23/0.53    r1_tarski(sK2,k1_xboole_0) | ~spl3_29),
% 1.23/0.53    inference(avatar_component_clause,[],[f581])).
% 1.23/0.53  fof(f581,plain,(
% 1.23/0.53    spl3_29 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.23/0.53  fof(f608,plain,(
% 1.23/0.53    ( ! [X0] : (v4_relat_1(sK2,X0)) ) | ~spl3_32),
% 1.23/0.53    inference(avatar_component_clause,[],[f607])).
% 1.23/0.53  fof(f607,plain,(
% 1.23/0.53    spl3_32 <=> ! [X0] : v4_relat_1(sK2,X0)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.23/0.53  fof(f760,plain,(
% 1.23/0.53    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | (~spl3_7 | spl3_8 | ~spl3_30)),
% 1.23/0.53    inference(forward_demodulation,[],[f712,f713])).
% 1.23/0.53  fof(f713,plain,(
% 1.23/0.53    k1_xboole_0 = sK1 | ~spl3_30),
% 1.23/0.53    inference(resolution,[],[f595,f121])).
% 1.23/0.53  fof(f595,plain,(
% 1.23/0.53    r1_tarski(sK1,k1_xboole_0) | ~spl3_30),
% 1.23/0.53    inference(avatar_component_clause,[],[f593])).
% 1.23/0.53  fof(f593,plain,(
% 1.23/0.53    spl3_30 <=> r1_tarski(sK1,k1_xboole_0)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.23/0.53  fof(f712,plain,(
% 1.23/0.53    ~v4_relat_1(sK1,k1_xboole_0) | (~spl3_7 | spl3_8)),
% 1.23/0.53    inference(forward_demodulation,[],[f260,f257])).
% 1.23/0.53  fof(f257,plain,(
% 1.23/0.53    k1_xboole_0 = sK0 | ~spl3_7),
% 1.23/0.53    inference(avatar_component_clause,[],[f255])).
% 1.23/0.53  fof(f255,plain,(
% 1.23/0.53    spl3_7 <=> k1_xboole_0 = sK0),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.23/0.53  fof(f260,plain,(
% 1.23/0.53    ~v4_relat_1(sK1,sK0) | spl3_8),
% 1.23/0.53    inference(avatar_component_clause,[],[f259])).
% 1.23/0.53  fof(f259,plain,(
% 1.23/0.53    spl3_8 <=> v4_relat_1(sK1,sK0)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.23/0.53  fof(f697,plain,(
% 1.23/0.53    spl3_29 | ~spl3_7),
% 1.23/0.53    inference(avatar_split_clause,[],[f696,f255,f581])).
% 1.23/0.53  fof(f696,plain,(
% 1.23/0.53    r1_tarski(sK2,k1_xboole_0) | ~spl3_7),
% 1.23/0.53    inference(forward_demodulation,[],[f674,f88])).
% 1.23/0.53  fof(f88,plain,(
% 1.23/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.23/0.53    inference(equality_resolution,[],[f78])).
% 1.23/0.53  fof(f78,plain,(
% 1.23/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.23/0.53    inference(cnf_transformation,[],[f52])).
% 1.23/0.53  fof(f52,plain,(
% 1.23/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.23/0.53    inference(flattening,[],[f51])).
% 1.23/0.53  fof(f51,plain,(
% 1.23/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.23/0.53    inference(nnf_transformation,[],[f2])).
% 1.23/0.53  fof(f2,axiom,(
% 1.23/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.23/0.53  fof(f674,plain,(
% 1.23/0.53    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)) | ~spl3_7),
% 1.23/0.53    inference(backward_demodulation,[],[f445,f257])).
% 1.23/0.53  fof(f445,plain,(
% 1.23/0.53    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK0))),
% 1.23/0.53    inference(subsumption_resolution,[],[f440,f97])).
% 1.23/0.53  fof(f97,plain,(
% 1.23/0.53    v1_relat_1(sK2)),
% 1.23/0.53    inference(resolution,[],[f81,f54])).
% 1.23/0.53  fof(f54,plain,(
% 1.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(cnf_transformation,[],[f45])).
% 1.23/0.53  fof(f45,plain,(
% 1.23/0.53    (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) & sK0 = k2_relset_1(sK0,sK0,sK2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f44,f43])).
% 1.23/0.53  fof(f43,plain,(
% 1.23/0.53    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) & sK0 = k2_relset_1(sK0,sK0,X2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f44,plain,(
% 1.23/0.53    ? [X2] : (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) & sK0 = k2_relset_1(sK0,sK0,X2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) => (sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) & sK0 = k2_relset_1(sK0,sK0,sK2) & sK0 = k2_relset_1(sK0,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f23,plain,(
% 1.23/0.53    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.23/0.53    inference(flattening,[],[f22])).
% 1.23/0.53  fof(f22,plain,(
% 1.23/0.53    ? [X0,X1] : (? [X2] : ((k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & (k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.23/0.53    inference(ennf_transformation,[],[f21])).
% 1.23/0.53  fof(f21,negated_conjecture,(
% 1.23/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 1.23/0.53    inference(negated_conjecture,[],[f20])).
% 1.23/0.53  fof(f20,conjecture,(
% 1.23/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).
% 1.23/0.53  fof(f81,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f35])).
% 1.23/0.53  fof(f35,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(ennf_transformation,[],[f16])).
% 1.23/0.53  fof(f16,axiom,(
% 1.23/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.23/0.53  fof(f440,plain,(
% 1.23/0.53    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),sK0)) | ~v1_relat_1(sK2)),
% 1.23/0.53    inference(superposition,[],[f59,f414])).
% 1.23/0.53  fof(f414,plain,(
% 1.23/0.53    sK0 = k2_relat_1(sK2)),
% 1.23/0.53    inference(subsumption_resolution,[],[f409,f54])).
% 1.23/0.53  fof(f409,plain,(
% 1.23/0.53    sK0 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(superposition,[],[f82,f56])).
% 1.23/0.53  fof(f56,plain,(
% 1.23/0.53    sK0 = k2_relset_1(sK0,sK0,sK2)),
% 1.23/0.53    inference(cnf_transformation,[],[f45])).
% 1.23/0.53  fof(f82,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f36,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(ennf_transformation,[],[f18])).
% 1.23/0.53  fof(f18,axiom,(
% 1.23/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.23/0.53  fof(f59,plain,(
% 1.23/0.53    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f24])).
% 1.23/0.53  fof(f24,plain,(
% 1.23/0.53    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f13])).
% 1.23/0.53  fof(f13,axiom,(
% 1.23/0.53    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.23/0.53  fof(f695,plain,(
% 1.23/0.53    spl3_30 | ~spl3_7),
% 1.23/0.53    inference(avatar_split_clause,[],[f694,f255,f593])).
% 1.23/0.53  fof(f694,plain,(
% 1.23/0.53    r1_tarski(sK1,k1_xboole_0) | ~spl3_7),
% 1.23/0.53    inference(forward_demodulation,[],[f673,f88])).
% 1.23/0.53  fof(f673,plain,(
% 1.23/0.53    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) | ~spl3_7),
% 1.23/0.53    inference(backward_demodulation,[],[f435,f257])).
% 1.23/0.53  fof(f435,plain,(
% 1.23/0.53    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))),
% 1.23/0.53    inference(subsumption_resolution,[],[f430,f96])).
% 1.23/0.53  fof(f96,plain,(
% 1.23/0.53    v1_relat_1(sK1)),
% 1.23/0.53    inference(resolution,[],[f81,f53])).
% 1.23/0.53  fof(f53,plain,(
% 1.23/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(cnf_transformation,[],[f45])).
% 1.23/0.53  fof(f430,plain,(
% 1.23/0.53    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | ~v1_relat_1(sK1)),
% 1.23/0.53    inference(superposition,[],[f59,f413])).
% 1.23/0.53  fof(f413,plain,(
% 1.23/0.53    sK0 = k2_relat_1(sK1)),
% 1.23/0.53    inference(subsumption_resolution,[],[f408,f53])).
% 1.23/0.53  fof(f408,plain,(
% 1.23/0.53    sK0 = k2_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(superposition,[],[f82,f55])).
% 1.23/0.53  fof(f55,plain,(
% 1.23/0.53    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.23/0.53    inference(cnf_transformation,[],[f45])).
% 1.23/0.53  fof(f652,plain,(
% 1.23/0.53    spl3_22 | ~spl3_16),
% 1.23/0.53    inference(avatar_split_clause,[],[f651,f418,f513])).
% 1.23/0.53  fof(f513,plain,(
% 1.23/0.53    spl3_22 <=> m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.23/0.53  fof(f418,plain,(
% 1.23/0.53    spl3_16 <=> m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.23/0.53  fof(f651,plain,(
% 1.23/0.53    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_16),
% 1.23/0.53    inference(subsumption_resolution,[],[f650,f54])).
% 1.23/0.53  fof(f650,plain,(
% 1.23/0.53    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_16),
% 1.23/0.53    inference(subsumption_resolution,[],[f644,f53])).
% 1.23/0.53  fof(f644,plain,(
% 1.23/0.53    m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_16),
% 1.23/0.53    inference(superposition,[],[f419,f84])).
% 1.23/0.53  fof(f84,plain,(
% 1.23/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f40])).
% 1.23/0.53  fof(f40,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(flattening,[],[f39])).
% 1.23/0.53  fof(f39,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.23/0.53    inference(ennf_transformation,[],[f19])).
% 1.23/0.53  fof(f19,axiom,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.23/0.53  fof(f419,plain,(
% 1.23/0.53    m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_16),
% 1.23/0.53    inference(avatar_component_clause,[],[f418])).
% 1.23/0.53  fof(f630,plain,(
% 1.23/0.53    spl3_7 | spl3_8),
% 1.23/0.53    inference(avatar_split_clause,[],[f319,f259,f255])).
% 1.23/0.53  fof(f319,plain,(
% 1.23/0.53    v4_relat_1(sK1,sK0) | k1_xboole_0 = sK0),
% 1.23/0.53    inference(duplicate_literal_removal,[],[f316])).
% 1.23/0.53  fof(f316,plain,(
% 1.23/0.53    v4_relat_1(sK1,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.23/0.53    inference(superposition,[],[f240,f79])).
% 1.23/0.53  fof(f79,plain,(
% 1.23/0.53    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.23/0.53    inference(cnf_transformation,[],[f34])).
% 1.23/0.53  fof(f34,plain,(
% 1.23/0.53    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.23/0.53    inference(ennf_transformation,[],[f11])).
% 1.23/0.53  fof(f11,axiom,(
% 1.23/0.53    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 1.23/0.53  fof(f240,plain,(
% 1.23/0.53    v4_relat_1(sK1,k1_relat_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(subsumption_resolution,[],[f238,f65])).
% 1.23/0.53  fof(f65,plain,(
% 1.23/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f8])).
% 1.23/0.53  fof(f8,axiom,(
% 1.23/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.23/0.53  fof(f238,plain,(
% 1.23/0.53    v4_relat_1(sK1,k1_relat_1(k2_zfmisc_1(sK0,sK0))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.23/0.53    inference(resolution,[],[f212,f116])).
% 1.23/0.53  fof(f116,plain,(
% 1.23/0.53    ( ! [X2] : (v4_relat_1(X2,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.23/0.53    inference(resolution,[],[f68,f86])).
% 1.23/0.53  fof(f86,plain,(
% 1.23/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.23/0.53    inference(equality_resolution,[],[f72])).
% 1.23/0.53  fof(f72,plain,(
% 1.23/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.23/0.53    inference(cnf_transformation,[],[f49])).
% 1.23/0.53  fof(f68,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f47])).
% 1.23/0.53  fof(f47,plain,(
% 1.23/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.23/0.53    inference(nnf_transformation,[],[f29])).
% 1.23/0.53  fof(f29,plain,(
% 1.23/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.23/0.53    inference(ennf_transformation,[],[f7])).
% 1.23/0.53  fof(f7,axiom,(
% 1.23/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.23/0.53  fof(f212,plain,(
% 1.23/0.53    ( ! [X0] : (~v4_relat_1(k2_zfmisc_1(sK0,sK0),X0) | v4_relat_1(sK1,X0)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f208,f65])).
% 1.23/0.53  fof(f208,plain,(
% 1.23/0.53    ( ! [X0] : (v4_relat_1(sK1,X0) | ~v4_relat_1(k2_zfmisc_1(sK0,sK0),X0) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0))) )),
% 1.23/0.53    inference(resolution,[],[f70,f53])).
% 1.23/0.53  fof(f70,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | v4_relat_1(X2,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f33])).
% 1.23/0.53  fof(f33,plain,(
% 1.23/0.53    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.23/0.53    inference(flattening,[],[f32])).
% 1.23/0.53  fof(f32,plain,(
% 1.23/0.53    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.23/0.53    inference(ennf_transformation,[],[f6])).
% 1.23/0.53  fof(f6,axiom,(
% 1.23/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).
% 1.23/0.53  fof(f629,plain,(
% 1.23/0.53    ~spl3_8 | spl3_23),
% 1.23/0.53    inference(avatar_split_clause,[],[f543,f517,f259])).
% 1.23/0.53  fof(f517,plain,(
% 1.23/0.53    spl3_23 <=> sK0 = k2_relat_1(k5_relat_1(sK2,sK1))),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.23/0.53  fof(f543,plain,(
% 1.23/0.53    ~v4_relat_1(sK1,sK0) | spl3_23),
% 1.23/0.53    inference(subsumption_resolution,[],[f542,f96])).
% 1.23/0.53  fof(f542,plain,(
% 1.23/0.53    ~v1_relat_1(sK1) | ~v4_relat_1(sK1,sK0) | spl3_23),
% 1.23/0.53    inference(subsumption_resolution,[],[f541,f413])).
% 1.23/0.53  fof(f541,plain,(
% 1.23/0.53    sK0 != k2_relat_1(sK1) | ~v1_relat_1(sK1) | ~v4_relat_1(sK1,sK0) | spl3_23),
% 1.23/0.53    inference(superposition,[],[f540,f197])).
% 1.23/0.53  fof(f197,plain,(
% 1.23/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.23/0.53    inference(duplicate_literal_removal,[],[f196])).
% 1.23/0.53  fof(f196,plain,(
% 1.23/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.23/0.53    inference(superposition,[],[f66,f69])).
% 1.23/0.53  fof(f69,plain,(
% 1.23/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f31])).
% 1.23/0.53  fof(f31,plain,(
% 1.23/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.23/0.53    inference(flattening,[],[f30])).
% 1.23/0.53  fof(f30,plain,(
% 1.23/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.23/0.53    inference(ennf_transformation,[],[f12])).
% 1.23/0.53  fof(f12,axiom,(
% 1.23/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.23/0.53  fof(f66,plain,(
% 1.23/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f28])).
% 1.23/0.53  fof(f28,plain,(
% 1.23/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.23/0.53    inference(ennf_transformation,[],[f9])).
% 1.23/0.53  fof(f9,axiom,(
% 1.23/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.23/0.53  fof(f540,plain,(
% 1.23/0.53    sK0 != k9_relat_1(sK1,sK0) | spl3_23),
% 1.23/0.53    inference(forward_demodulation,[],[f539,f414])).
% 1.23/0.53  fof(f539,plain,(
% 1.23/0.53    sK0 != k9_relat_1(sK1,k2_relat_1(sK2)) | spl3_23),
% 1.23/0.53    inference(subsumption_resolution,[],[f538,f97])).
% 1.23/0.53  fof(f538,plain,(
% 1.23/0.53    sK0 != k9_relat_1(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | spl3_23),
% 1.23/0.53    inference(subsumption_resolution,[],[f536,f96])).
% 1.23/0.53  fof(f536,plain,(
% 1.23/0.53    sK0 != k9_relat_1(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | spl3_23),
% 1.23/0.53    inference(superposition,[],[f519,f64])).
% 1.23/0.53  fof(f64,plain,(
% 1.23/0.53    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f27])).
% 1.23/0.53  fof(f27,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f10])).
% 1.23/0.53  fof(f10,axiom,(
% 1.23/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 1.23/0.53  fof(f519,plain,(
% 1.23/0.53    sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) | spl3_23),
% 1.23/0.53    inference(avatar_component_clause,[],[f517])).
% 1.23/0.53  fof(f609,plain,(
% 1.23/0.53    spl3_32 | ~spl3_7),
% 1.23/0.53    inference(avatar_split_clause,[],[f605,f255,f607])).
% 1.23/0.53  fof(f605,plain,(
% 1.23/0.53    ( ! [X0] : (k1_xboole_0 != sK0 | v4_relat_1(sK2,X0)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f437,f97])).
% 1.23/0.53  fof(f437,plain,(
% 1.23/0.53    ( ! [X0] : (k1_xboole_0 != sK0 | ~v1_relat_1(sK2) | v4_relat_1(sK2,X0)) )),
% 1.23/0.53    inference(superposition,[],[f178,f414])).
% 1.23/0.53  fof(f178,plain,(
% 1.23/0.53    ( ! [X4,X3] : (k1_xboole_0 != k2_relat_1(X3) | ~v1_relat_1(X3) | v4_relat_1(X3,X4)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f174,f94])).
% 1.23/0.53  fof(f174,plain,(
% 1.23/0.53    ( ! [X4,X3] : (~r1_tarski(k1_xboole_0,X4) | v4_relat_1(X3,X4) | ~v1_relat_1(X3) | k1_xboole_0 != k2_relat_1(X3)) )),
% 1.23/0.53    inference(duplicate_literal_removal,[],[f168])).
% 1.23/0.53  fof(f168,plain,(
% 1.23/0.53    ( ! [X4,X3] : (~r1_tarski(k1_xboole_0,X4) | v4_relat_1(X3,X4) | ~v1_relat_1(X3) | k1_xboole_0 != k2_relat_1(X3) | ~v1_relat_1(X3)) )),
% 1.23/0.53    inference(superposition,[],[f68,f63])).
% 1.23/0.53  fof(f63,plain,(
% 1.23/0.53    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f46])).
% 1.23/0.53  fof(f46,plain,(
% 1.23/0.53    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.23/0.53    inference(nnf_transformation,[],[f26])).
% 1.23/0.53  fof(f26,plain,(
% 1.23/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f15])).
% 1.23/0.53  fof(f15,axiom,(
% 1.23/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.23/0.53  fof(f527,plain,(
% 1.23/0.53    spl3_16),
% 1.23/0.53    inference(avatar_contradiction_clause,[],[f526])).
% 1.23/0.53  fof(f526,plain,(
% 1.23/0.53    $false | spl3_16),
% 1.23/0.53    inference(subsumption_resolution,[],[f525,f54])).
% 1.23/0.53  fof(f525,plain,(
% 1.23/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_16),
% 1.23/0.53    inference(subsumption_resolution,[],[f522,f53])).
% 1.23/0.53  fof(f522,plain,(
% 1.23/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_16),
% 1.23/0.53    inference(resolution,[],[f420,f85])).
% 1.23/0.53  fof(f85,plain,(
% 1.23/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f42])).
% 1.23/0.53  fof(f42,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.23/0.53    inference(flattening,[],[f41])).
% 1.23/0.53  fof(f41,plain,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.23/0.53    inference(ennf_transformation,[],[f17])).
% 1.23/0.53  fof(f17,axiom,(
% 1.23/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 1.23/0.53  fof(f420,plain,(
% 1.23/0.53    ~m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_16),
% 1.23/0.53    inference(avatar_component_clause,[],[f418])).
% 1.23/0.53  fof(f520,plain,(
% 1.23/0.53    ~spl3_22 | ~spl3_23),
% 1.23/0.53    inference(avatar_split_clause,[],[f511,f517,f513])).
% 1.23/0.53  fof(f511,plain,(
% 1.23/0.53    sK0 != k2_relat_1(k5_relat_1(sK2,sK1)) | ~m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(superposition,[],[f456,f82])).
% 1.23/0.53  fof(f456,plain,(
% 1.23/0.53    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))),
% 1.23/0.53    inference(subsumption_resolution,[],[f455,f54])).
% 1.23/0.53  fof(f455,plain,(
% 1.23/0.53    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(subsumption_resolution,[],[f454,f53])).
% 1.23/0.53  fof(f454,plain,(
% 1.23/0.53    sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.23/0.53    inference(superposition,[],[f57,f84])).
% 1.23/0.53  fof(f57,plain,(
% 1.23/0.53    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))),
% 1.23/0.53    inference(cnf_transformation,[],[f45])).
% 1.23/0.53  % SZS output end Proof for theBenchmark
% 1.23/0.53  % (23186)------------------------------
% 1.23/0.53  % (23186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (23186)Termination reason: Refutation
% 1.23/0.53  
% 1.23/0.53  % (23186)Memory used [KB]: 6396
% 1.23/0.53  % (23186)Time elapsed: 0.117 s
% 1.23/0.53  % (23186)------------------------------
% 1.23/0.53  % (23186)------------------------------
% 1.23/0.53  % (23196)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.23/0.53  % (23181)Success in time 0.172 s
%------------------------------------------------------------------------------
