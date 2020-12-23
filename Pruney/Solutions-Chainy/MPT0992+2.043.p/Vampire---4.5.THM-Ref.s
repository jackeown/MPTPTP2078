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
% DateTime   : Thu Dec  3 13:03:16 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 588 expanded)
%              Number of leaves         :   30 ( 158 expanded)
%              Depth                    :   17
%              Number of atoms          :  564 (3186 expanded)
%              Number of equality atoms :  110 ( 731 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2597,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f109,f162,f533,f643,f708,f770,f1443,f1723,f2185,f2202,f2222,f2248,f2596])).

fof(f2596,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f2595])).

fof(f2595,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f2594,f2547])).

fof(f2547,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f273,f274])).

fof(f274,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_4 ),
    inference(resolution,[],[f228,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f228,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f224,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f224,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f136,f103])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f136,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f51,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f273,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f219,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f219,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f50,f103])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f2594,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f2593,f233])).

fof(f233,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f229,f69])).

fof(f229,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f52,f108])).

fof(f52,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f2593,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f2302,f103])).

fof(f2302,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,sK1)
    | spl4_2
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f1133,f1800])).

fof(f1800,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_40 ),
    inference(resolution,[],[f1743,f69])).

fof(f1743,plain,
    ( ! [X6] : r1_tarski(k7_relat_1(k1_xboole_0,X6),k1_xboole_0)
    | ~ spl4_40 ),
    inference(resolution,[],[f1522,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1522,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f1521])).

fof(f1521,plain,
    ( spl4_40
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1133,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1132,f879])).

fof(f879,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f49,f840])).

fof(f840,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_25 ),
    inference(resolution,[],[f827,f69])).

fof(f827,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_25 ),
    inference(resolution,[],[f598,f72])).

fof(f598,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl4_25
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f1132,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | spl4_2
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1117,f881])).

fof(f881,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f51,f840])).

fof(f1117,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | spl4_2
    | ~ spl4_25 ),
    inference(superposition,[],[f883,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f883,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,k1_xboole_0,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f95,f840])).

fof(f95,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2248,plain,
    ( ~ spl4_4
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f2247])).

fof(f2247,plain,
    ( $false
    | ~ spl4_4
    | spl4_25 ),
    inference(subsumption_resolution,[],[f227,f599])).

fof(f599,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f597])).

fof(f227,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f220,f86])).

fof(f220,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f51,f103])).

fof(f2222,plain,
    ( spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f2221,f123,f102])).

fof(f123,plain,
    ( spl4_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f2221,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f446,f51])).

fof(f446,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f2202,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f2201])).

fof(f2201,plain,
    ( $false
    | spl4_22 ),
    inference(subsumption_resolution,[],[f2200,f148])).

fof(f148,plain,(
    ! [X7] : v1_relat_1(k7_relat_1(sK3,X7)) ),
    inference(resolution,[],[f134,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f134,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2200,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_22 ),
    inference(forward_demodulation,[],[f2199,f139])).

fof(f139,plain,(
    ! [X2] : k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f130,plain,(
    ! [X2] :
      ( k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f51,f57])).

fof(f2199,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_22 ),
    inference(subsumption_resolution,[],[f2198,f2160])).

fof(f2160,plain,(
    ! [X10] : v5_relat_1(k7_relat_1(sK3,X10),sK1) ),
    inference(resolution,[],[f2125,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2125,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f138,f139])).

fof(f138,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f129,f49])).

fof(f129,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f51,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f2198,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_22 ),
    inference(forward_demodulation,[],[f736,f139])).

fof(f736,plain,
    ( ~ v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_22 ),
    inference(resolution,[],[f532,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f532,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl4_22
  <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f2185,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f2184])).

fof(f2184,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_7
    | spl4_8 ),
    inference(subsumption_resolution,[],[f2183,f52])).

fof(f2183,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl4_3
    | ~ spl4_7
    | spl4_8 ),
    inference(forward_demodulation,[],[f2182,f551])).

fof(f551,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f547,f51])).

fof(f547,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(superposition,[],[f125,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f125,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f2182,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_3
    | spl4_8 ),
    inference(subsumption_resolution,[],[f2181,f134])).

fof(f2181,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | spl4_8 ),
    inference(trivial_inequality_removal,[],[f2180])).

fof(f2180,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | spl4_8 ),
    inference(superposition,[],[f2179,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f2179,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_3
    | spl4_8 ),
    inference(subsumption_resolution,[],[f2176,f1462])).

fof(f1462,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f1461,f49])).

fof(f1461,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f1455,f51])).

fof(f1455,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3 ),
    inference(superposition,[],[f98,f57])).

fof(f98,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2176,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_8 ),
    inference(superposition,[],[f2172,f64])).

fof(f2172,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_8 ),
    inference(forward_demodulation,[],[f195,f139])).

fof(f195,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_8
  <=> sK2 = k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1723,plain,
    ( ~ spl4_12
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f1722])).

fof(f1722,plain,
    ( $false
    | ~ spl4_12
    | spl4_40 ),
    inference(subsumption_resolution,[],[f1716,f251])).

fof(f251,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl4_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1716,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_40 ),
    inference(superposition,[],[f1537,f87])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1537,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_40 ),
    inference(resolution,[],[f1523,f78])).

fof(f1523,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f1521])).

fof(f1443,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f1442,f102,f93,f193,f97])).

fof(f1442,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f1440,f104])).

fof(f104,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f1440,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2 ),
    inference(resolution,[],[f95,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f770,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f768,f134])).

fof(f768,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_12 ),
    inference(subsumption_resolution,[],[f760,f453])).

fof(f453,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_12 ),
    inference(resolution,[],[f252,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f252,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f250])).

fof(f760,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f76,f656])).

fof(f656,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(resolution,[],[f146,f69])).

fof(f146,plain,(
    ! [X5] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X5)),X5) ),
    inference(resolution,[],[f134,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f708,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f707])).

fof(f707,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f706,f49])).

fof(f706,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_21 ),
    inference(subsumption_resolution,[],[f705,f51])).

fof(f705,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_21 ),
    inference(subsumption_resolution,[],[f704,f146])).

fof(f704,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_21 ),
    inference(superposition,[],[f528,f57])).

fof(f528,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl4_21
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f643,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | spl4_20 ),
    inference(subsumption_resolution,[],[f641,f49])).

fof(f641,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_20 ),
    inference(subsumption_resolution,[],[f640,f51])).

fof(f640,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_20 ),
    inference(subsumption_resolution,[],[f639,f148])).

fof(f639,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_20 ),
    inference(superposition,[],[f524,f57])).

fof(f524,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f522])).

fof(f522,plain,
    ( spl4_20
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f533,plain,
    ( ~ spl4_20
    | ~ spl4_21
    | ~ spl4_22
    | spl4_3 ),
    inference(avatar_split_clause,[],[f518,f97,f530,f526,f522])).

fof(f518,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_3 ),
    inference(resolution,[],[f99,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f99,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f162,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f160,f49])).

fof(f160,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f158,f51])).

fof(f158,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(resolution,[],[f91,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f109,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f53,f106,f102])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f97,f93,f89])).

fof(f54,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (5490)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (5497)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (5487)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (5486)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (5488)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (5484)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (5481)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (5489)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (5501)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (5492)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (5496)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (5485)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (5498)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (5499)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (5500)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (5482)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5483)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (5502)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (5493)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5494)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (5491)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.72/0.58  % (5501)Refutation found. Thanks to Tanya!
% 1.72/0.58  % SZS status Theorem for theBenchmark
% 1.72/0.58  % SZS output start Proof for theBenchmark
% 1.72/0.58  fof(f2597,plain,(
% 1.72/0.58    $false),
% 1.72/0.58    inference(avatar_sat_refutation,[],[f100,f109,f162,f533,f643,f708,f770,f1443,f1723,f2185,f2202,f2222,f2248,f2596])).
% 1.72/0.58  fof(f2596,plain,(
% 1.72/0.58    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_25 | ~spl4_40),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f2595])).
% 1.72/0.58  fof(f2595,plain,(
% 1.72/0.58    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_25 | ~spl4_40)),
% 1.72/0.58    inference(subsumption_resolution,[],[f2594,f2547])).
% 1.72/0.58  fof(f2547,plain,(
% 1.72/0.58    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.72/0.58    inference(backward_demodulation,[],[f273,f274])).
% 1.72/0.58  fof(f274,plain,(
% 1.72/0.58    k1_xboole_0 = sK3 | ~spl4_4),
% 1.72/0.58    inference(resolution,[],[f228,f69])).
% 1.72/0.58  fof(f69,plain,(
% 1.72/0.58    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f31])).
% 1.72/0.58  fof(f31,plain,(
% 1.72/0.58    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.72/0.58    inference(ennf_transformation,[],[f2])).
% 1.72/0.58  fof(f2,axiom,(
% 1.72/0.58    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.72/0.58  fof(f228,plain,(
% 1.72/0.58    r1_tarski(sK3,k1_xboole_0) | ~spl4_4),
% 1.72/0.58    inference(forward_demodulation,[],[f224,f86])).
% 1.72/0.58  fof(f86,plain,(
% 1.72/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.72/0.58    inference(equality_resolution,[],[f67])).
% 1.72/0.58  fof(f67,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.72/0.58    inference(cnf_transformation,[],[f46])).
% 1.72/0.58  fof(f46,plain,(
% 1.72/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.72/0.58    inference(flattening,[],[f45])).
% 1.72/0.58  fof(f45,plain,(
% 1.72/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.72/0.58    inference(nnf_transformation,[],[f3])).
% 1.72/0.58  fof(f3,axiom,(
% 1.72/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.72/0.58  fof(f224,plain,(
% 1.72/0.58    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl4_4),
% 1.72/0.58    inference(backward_demodulation,[],[f136,f103])).
% 1.72/0.58  fof(f103,plain,(
% 1.72/0.58    k1_xboole_0 = sK1 | ~spl4_4),
% 1.72/0.58    inference(avatar_component_clause,[],[f102])).
% 1.72/0.58  fof(f102,plain,(
% 1.72/0.58    spl4_4 <=> k1_xboole_0 = sK1),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.72/0.58  fof(f136,plain,(
% 1.72/0.58    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.72/0.58    inference(resolution,[],[f51,f72])).
% 1.72/0.58  fof(f72,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f47])).
% 1.72/0.58  fof(f47,plain,(
% 1.72/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.72/0.58    inference(nnf_transformation,[],[f4])).
% 1.72/0.58  fof(f4,axiom,(
% 1.72/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.72/0.58  fof(f51,plain,(
% 1.72/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.72/0.58    inference(cnf_transformation,[],[f43])).
% 1.72/0.58  fof(f43,plain,(
% 1.72/0.58    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.72/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f42])).
% 1.72/0.58  fof(f42,plain,(
% 1.72/0.58    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.72/0.58    introduced(choice_axiom,[])).
% 1.72/0.58  fof(f21,plain,(
% 1.72/0.58    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.72/0.58    inference(flattening,[],[f20])).
% 1.72/0.58  fof(f20,plain,(
% 1.72/0.58    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.72/0.58    inference(ennf_transformation,[],[f18])).
% 1.72/0.58  fof(f18,negated_conjecture,(
% 1.72/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.72/0.58    inference(negated_conjecture,[],[f17])).
% 1.72/0.58  fof(f17,conjecture,(
% 1.72/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.72/0.58  fof(f273,plain,(
% 1.72/0.58    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.72/0.58    inference(forward_demodulation,[],[f219,f108])).
% 1.72/0.58  fof(f108,plain,(
% 1.72/0.58    k1_xboole_0 = sK0 | ~spl4_5),
% 1.72/0.58    inference(avatar_component_clause,[],[f106])).
% 1.72/0.58  fof(f106,plain,(
% 1.72/0.58    spl4_5 <=> k1_xboole_0 = sK0),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.72/0.58  fof(f219,plain,(
% 1.72/0.58    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 1.72/0.58    inference(backward_demodulation,[],[f50,f103])).
% 1.72/0.58  fof(f50,plain,(
% 1.72/0.58    v1_funct_2(sK3,sK0,sK1)),
% 1.72/0.58    inference(cnf_transformation,[],[f43])).
% 1.72/0.58  fof(f2594,plain,(
% 1.72/0.58    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_25 | ~spl4_40)),
% 1.72/0.58    inference(forward_demodulation,[],[f2593,f233])).
% 1.72/0.58  fof(f233,plain,(
% 1.72/0.58    k1_xboole_0 = sK2 | ~spl4_5),
% 1.72/0.58    inference(resolution,[],[f229,f69])).
% 1.72/0.58  fof(f229,plain,(
% 1.72/0.58    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.72/0.58    inference(backward_demodulation,[],[f52,f108])).
% 1.72/0.58  fof(f52,plain,(
% 1.72/0.58    r1_tarski(sK2,sK0)),
% 1.72/0.58    inference(cnf_transformation,[],[f43])).
% 1.72/0.58  fof(f2593,plain,(
% 1.72/0.58    ~v1_funct_2(k1_xboole_0,sK2,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_25 | ~spl4_40)),
% 1.72/0.58    inference(forward_demodulation,[],[f2302,f103])).
% 1.72/0.58  fof(f2302,plain,(
% 1.72/0.58    ~v1_funct_2(k1_xboole_0,sK2,sK1) | (spl4_2 | ~spl4_25 | ~spl4_40)),
% 1.72/0.58    inference(forward_demodulation,[],[f1133,f1800])).
% 1.72/0.58  fof(f1800,plain,(
% 1.72/0.58    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl4_40),
% 1.72/0.58    inference(resolution,[],[f1743,f69])).
% 1.72/0.58  fof(f1743,plain,(
% 1.72/0.58    ( ! [X6] : (r1_tarski(k7_relat_1(k1_xboole_0,X6),k1_xboole_0)) ) | ~spl4_40),
% 1.72/0.58    inference(resolution,[],[f1522,f77])).
% 1.72/0.58  fof(f77,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f38])).
% 1.72/0.58  fof(f38,plain,(
% 1.72/0.58    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f8])).
% 1.72/0.58  fof(f8,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.72/0.58  fof(f1522,plain,(
% 1.72/0.58    v1_relat_1(k1_xboole_0) | ~spl4_40),
% 1.72/0.58    inference(avatar_component_clause,[],[f1521])).
% 1.72/0.58  fof(f1521,plain,(
% 1.72/0.58    spl4_40 <=> v1_relat_1(k1_xboole_0)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.72/0.58  fof(f1133,plain,(
% 1.72/0.58    ~v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1) | (spl4_2 | ~spl4_25)),
% 1.72/0.58    inference(subsumption_resolution,[],[f1132,f879])).
% 1.72/0.58  fof(f879,plain,(
% 1.72/0.58    v1_funct_1(k1_xboole_0) | ~spl4_25),
% 1.72/0.58    inference(backward_demodulation,[],[f49,f840])).
% 1.72/0.58  fof(f840,plain,(
% 1.72/0.58    k1_xboole_0 = sK3 | ~spl4_25),
% 1.72/0.58    inference(resolution,[],[f827,f69])).
% 1.72/0.58  fof(f827,plain,(
% 1.72/0.58    r1_tarski(sK3,k1_xboole_0) | ~spl4_25),
% 1.72/0.58    inference(resolution,[],[f598,f72])).
% 1.72/0.58  fof(f598,plain,(
% 1.72/0.58    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_25),
% 1.72/0.58    inference(avatar_component_clause,[],[f597])).
% 1.72/0.58  fof(f597,plain,(
% 1.72/0.58    spl4_25 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.72/0.58  fof(f49,plain,(
% 1.72/0.58    v1_funct_1(sK3)),
% 1.72/0.58    inference(cnf_transformation,[],[f43])).
% 1.72/0.58  fof(f1132,plain,(
% 1.72/0.58    ~v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1) | ~v1_funct_1(k1_xboole_0) | (spl4_2 | ~spl4_25)),
% 1.72/0.58    inference(subsumption_resolution,[],[f1117,f881])).
% 1.72/0.58  fof(f881,plain,(
% 1.72/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_25),
% 1.72/0.58    inference(backward_demodulation,[],[f51,f840])).
% 1.72/0.58  fof(f1117,plain,(
% 1.72/0.58    ~v1_funct_2(k7_relat_1(k1_xboole_0,sK2),sK2,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k1_xboole_0) | (spl4_2 | ~spl4_25)),
% 1.72/0.58    inference(superposition,[],[f883,f57])).
% 1.72/0.58  fof(f57,plain,(
% 1.72/0.58    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f25])).
% 1.72/0.58  fof(f25,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.72/0.58    inference(flattening,[],[f24])).
% 1.72/0.58  fof(f24,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.72/0.58    inference(ennf_transformation,[],[f16])).
% 1.72/0.58  fof(f16,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.72/0.58  fof(f883,plain,(
% 1.72/0.58    ~v1_funct_2(k2_partfun1(sK0,sK1,k1_xboole_0,sK2),sK2,sK1) | (spl4_2 | ~spl4_25)),
% 1.72/0.58    inference(backward_demodulation,[],[f95,f840])).
% 1.72/0.58  fof(f95,plain,(
% 1.72/0.58    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.72/0.58    inference(avatar_component_clause,[],[f93])).
% 1.72/0.58  fof(f93,plain,(
% 1.72/0.58    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.72/0.58  fof(f2248,plain,(
% 1.72/0.58    ~spl4_4 | spl4_25),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f2247])).
% 1.72/0.58  fof(f2247,plain,(
% 1.72/0.58    $false | (~spl4_4 | spl4_25)),
% 1.72/0.58    inference(subsumption_resolution,[],[f227,f599])).
% 1.72/0.58  fof(f599,plain,(
% 1.72/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl4_25),
% 1.72/0.58    inference(avatar_component_clause,[],[f597])).
% 1.72/0.58  fof(f227,plain,(
% 1.72/0.58    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_4),
% 1.72/0.58    inference(forward_demodulation,[],[f220,f86])).
% 1.72/0.58  fof(f220,plain,(
% 1.72/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_4),
% 1.72/0.58    inference(backward_demodulation,[],[f51,f103])).
% 1.72/0.58  fof(f2222,plain,(
% 1.72/0.58    spl4_4 | spl4_7),
% 1.72/0.58    inference(avatar_split_clause,[],[f2221,f123,f102])).
% 1.72/0.58  fof(f123,plain,(
% 1.72/0.58    spl4_7 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.72/0.58  fof(f2221,plain,(
% 1.72/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 1.72/0.58    inference(subsumption_resolution,[],[f446,f51])).
% 1.72/0.58  fof(f446,plain,(
% 1.72/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.72/0.58    inference(resolution,[],[f50,f58])).
% 1.72/0.58  fof(f58,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f44])).
% 1.72/0.58  fof(f44,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.58    inference(nnf_transformation,[],[f27])).
% 1.72/0.58  fof(f27,plain,(
% 1.72/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.58    inference(flattening,[],[f26])).
% 1.72/0.58  fof(f26,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.58    inference(ennf_transformation,[],[f14])).
% 1.72/0.58  fof(f14,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.72/0.58  fof(f2202,plain,(
% 1.72/0.58    spl4_22),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f2201])).
% 1.72/0.58  fof(f2201,plain,(
% 1.72/0.58    $false | spl4_22),
% 1.72/0.58    inference(subsumption_resolution,[],[f2200,f148])).
% 1.72/0.58  fof(f148,plain,(
% 1.72/0.58    ( ! [X7] : (v1_relat_1(k7_relat_1(sK3,X7))) )),
% 1.72/0.58    inference(resolution,[],[f134,f79])).
% 1.72/0.58  fof(f79,plain,(
% 1.72/0.58    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f40])).
% 1.72/0.58  fof(f40,plain,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.72/0.58    inference(ennf_transformation,[],[f6])).
% 1.72/0.58  fof(f6,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.72/0.58  fof(f134,plain,(
% 1.72/0.58    v1_relat_1(sK3)),
% 1.72/0.58    inference(resolution,[],[f51,f78])).
% 1.72/0.58  fof(f78,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f39])).
% 1.72/0.58  fof(f39,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.58    inference(ennf_transformation,[],[f10])).
% 1.72/0.58  fof(f10,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.72/0.58  fof(f2200,plain,(
% 1.72/0.58    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_22),
% 1.72/0.58    inference(forward_demodulation,[],[f2199,f139])).
% 1.72/0.58  fof(f139,plain,(
% 1.72/0.58    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)) )),
% 1.72/0.58    inference(subsumption_resolution,[],[f130,f49])).
% 1.72/0.58  fof(f130,plain,(
% 1.72/0.58    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) | ~v1_funct_1(sK3)) )),
% 1.72/0.58    inference(resolution,[],[f51,f57])).
% 1.72/0.58  fof(f2199,plain,(
% 1.72/0.58    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_22),
% 1.72/0.58    inference(subsumption_resolution,[],[f2198,f2160])).
% 1.72/0.58  fof(f2160,plain,(
% 1.72/0.58    ( ! [X10] : (v5_relat_1(k7_relat_1(sK3,X10),sK1)) )),
% 1.72/0.58    inference(resolution,[],[f2125,f80])).
% 1.72/0.58  fof(f80,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f41])).
% 1.72/0.58  fof(f41,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.58    inference(ennf_transformation,[],[f19])).
% 1.72/0.58  fof(f19,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.72/0.58    inference(pure_predicate_removal,[],[f11])).
% 1.72/0.58  fof(f11,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.72/0.58  fof(f2125,plain,(
% 1.72/0.58    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.72/0.58    inference(forward_demodulation,[],[f138,f139])).
% 1.72/0.58  fof(f138,plain,(
% 1.72/0.58    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.72/0.58    inference(subsumption_resolution,[],[f129,f49])).
% 1.72/0.58  fof(f129,plain,(
% 1.72/0.58    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.72/0.58    inference(resolution,[],[f51,f56])).
% 1.72/0.58  fof(f56,plain,(
% 1.72/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f23])).
% 1.72/0.58  fof(f23,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.72/0.58    inference(flattening,[],[f22])).
% 1.72/0.58  fof(f22,plain,(
% 1.72/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.72/0.58    inference(ennf_transformation,[],[f15])).
% 1.72/0.58  fof(f15,axiom,(
% 1.72/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.72/0.58  fof(f2198,plain,(
% 1.72/0.58    ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_22),
% 1.72/0.58    inference(forward_demodulation,[],[f736,f139])).
% 1.72/0.58  fof(f736,plain,(
% 1.72/0.58    ~v5_relat_1(k2_partfun1(sK0,sK1,sK3,sK2),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_22),
% 1.72/0.58    inference(resolution,[],[f532,f74])).
% 1.72/0.58  fof(f74,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f48])).
% 1.72/0.58  fof(f48,plain,(
% 1.72/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(nnf_transformation,[],[f36])).
% 1.72/0.58  fof(f36,plain,(
% 1.72/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f5])).
% 1.72/0.58  fof(f5,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.72/0.58  fof(f532,plain,(
% 1.72/0.58    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | spl4_22),
% 1.72/0.58    inference(avatar_component_clause,[],[f530])).
% 1.72/0.58  fof(f530,plain,(
% 1.72/0.58    spl4_22 <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.72/0.58  fof(f2185,plain,(
% 1.72/0.58    ~spl4_3 | ~spl4_7 | spl4_8),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f2184])).
% 1.72/0.58  fof(f2184,plain,(
% 1.72/0.58    $false | (~spl4_3 | ~spl4_7 | spl4_8)),
% 1.72/0.58    inference(subsumption_resolution,[],[f2183,f52])).
% 1.72/0.58  fof(f2183,plain,(
% 1.72/0.58    ~r1_tarski(sK2,sK0) | (~spl4_3 | ~spl4_7 | spl4_8)),
% 1.72/0.58    inference(forward_demodulation,[],[f2182,f551])).
% 1.72/0.58  fof(f551,plain,(
% 1.72/0.58    sK0 = k1_relat_1(sK3) | ~spl4_7),
% 1.72/0.58    inference(subsumption_resolution,[],[f547,f51])).
% 1.72/0.58  fof(f547,plain,(
% 1.72/0.58    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 1.72/0.58    inference(superposition,[],[f125,f64])).
% 1.72/0.58  fof(f64,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f28])).
% 1.72/0.58  fof(f28,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.58    inference(ennf_transformation,[],[f12])).
% 1.72/0.58  fof(f12,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.72/0.58  fof(f125,plain,(
% 1.72/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_7),
% 1.72/0.58    inference(avatar_component_clause,[],[f123])).
% 1.72/0.58  fof(f2182,plain,(
% 1.72/0.58    ~r1_tarski(sK2,k1_relat_1(sK3)) | (~spl4_3 | spl4_8)),
% 1.72/0.58    inference(subsumption_resolution,[],[f2181,f134])).
% 1.72/0.58  fof(f2181,plain,(
% 1.72/0.58    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | spl4_8)),
% 1.72/0.58    inference(trivial_inequality_removal,[],[f2180])).
% 1.72/0.58  fof(f2180,plain,(
% 1.72/0.58    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | spl4_8)),
% 1.72/0.58    inference(superposition,[],[f2179,f68])).
% 1.72/0.58  fof(f68,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f30])).
% 1.72/0.58  fof(f30,plain,(
% 1.72/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(flattening,[],[f29])).
% 1.72/0.58  fof(f29,plain,(
% 1.72/0.58    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f9])).
% 1.72/0.58  fof(f9,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.72/0.58  fof(f2179,plain,(
% 1.72/0.58    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_3 | spl4_8)),
% 1.72/0.58    inference(subsumption_resolution,[],[f2176,f1462])).
% 1.72/0.58  fof(f1462,plain,(
% 1.72/0.58    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.72/0.58    inference(subsumption_resolution,[],[f1461,f49])).
% 1.72/0.58  fof(f1461,plain,(
% 1.72/0.58    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | ~spl4_3),
% 1.72/0.58    inference(subsumption_resolution,[],[f1455,f51])).
% 1.72/0.58  fof(f1455,plain,(
% 1.72/0.58    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~spl4_3),
% 1.72/0.58    inference(superposition,[],[f98,f57])).
% 1.72/0.58  fof(f98,plain,(
% 1.72/0.58    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 1.72/0.58    inference(avatar_component_clause,[],[f97])).
% 1.72/0.58  fof(f97,plain,(
% 1.72/0.58    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.72/0.58  fof(f2176,plain,(
% 1.72/0.58    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_8),
% 1.72/0.58    inference(superposition,[],[f2172,f64])).
% 1.72/0.58  fof(f2172,plain,(
% 1.72/0.58    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_8),
% 1.72/0.58    inference(forward_demodulation,[],[f195,f139])).
% 1.72/0.58  fof(f195,plain,(
% 1.72/0.58    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_8),
% 1.72/0.58    inference(avatar_component_clause,[],[f193])).
% 1.72/0.58  fof(f193,plain,(
% 1.72/0.58    spl4_8 <=> sK2 = k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.72/0.58  fof(f1723,plain,(
% 1.72/0.58    ~spl4_12 | spl4_40),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f1722])).
% 1.72/0.58  fof(f1722,plain,(
% 1.72/0.58    $false | (~spl4_12 | spl4_40)),
% 1.72/0.58    inference(subsumption_resolution,[],[f1716,f251])).
% 1.72/0.58  fof(f251,plain,(
% 1.72/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_12),
% 1.72/0.58    inference(avatar_component_clause,[],[f250])).
% 1.72/0.58  fof(f250,plain,(
% 1.72/0.58    spl4_12 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.72/0.58  fof(f1716,plain,(
% 1.72/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_40),
% 1.72/0.58    inference(superposition,[],[f1537,f87])).
% 1.72/0.58  fof(f87,plain,(
% 1.72/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.72/0.58    inference(equality_resolution,[],[f66])).
% 1.72/0.58  fof(f66,plain,(
% 1.72/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.72/0.58    inference(cnf_transformation,[],[f46])).
% 1.72/0.58  fof(f1537,plain,(
% 1.72/0.58    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_40),
% 1.72/0.58    inference(resolution,[],[f1523,f78])).
% 1.72/0.58  fof(f1523,plain,(
% 1.72/0.58    ~v1_relat_1(k1_xboole_0) | spl4_40),
% 1.72/0.58    inference(avatar_component_clause,[],[f1521])).
% 1.72/0.58  fof(f1443,plain,(
% 1.72/0.58    ~spl4_3 | ~spl4_8 | spl4_2 | spl4_4),
% 1.72/0.58    inference(avatar_split_clause,[],[f1442,f102,f93,f193,f97])).
% 1.72/0.58  fof(f1442,plain,(
% 1.72/0.58    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | spl4_4)),
% 1.72/0.58    inference(subsumption_resolution,[],[f1440,f104])).
% 1.72/0.58  fof(f104,plain,(
% 1.72/0.58    k1_xboole_0 != sK1 | spl4_4),
% 1.72/0.58    inference(avatar_component_clause,[],[f102])).
% 1.72/0.58  fof(f1440,plain,(
% 1.72/0.58    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_2),
% 1.72/0.58    inference(resolution,[],[f95,f60])).
% 1.72/0.58  fof(f60,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.72/0.58    inference(cnf_transformation,[],[f44])).
% 1.72/0.58  fof(f770,plain,(
% 1.72/0.58    spl4_12),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f769])).
% 1.72/0.58  fof(f769,plain,(
% 1.72/0.58    $false | spl4_12),
% 1.72/0.58    inference(subsumption_resolution,[],[f768,f134])).
% 1.72/0.58  fof(f768,plain,(
% 1.72/0.58    ~v1_relat_1(sK3) | spl4_12),
% 1.72/0.58    inference(subsumption_resolution,[],[f760,f453])).
% 1.72/0.58  fof(f453,plain,(
% 1.72/0.58    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_12),
% 1.72/0.58    inference(resolution,[],[f252,f73])).
% 1.72/0.58  fof(f73,plain,(
% 1.72/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f47])).
% 1.72/0.58  fof(f252,plain,(
% 1.72/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_12),
% 1.72/0.58    inference(avatar_component_clause,[],[f250])).
% 1.72/0.58  fof(f760,plain,(
% 1.72/0.58    r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(sK3)),
% 1.72/0.58    inference(superposition,[],[f76,f656])).
% 1.72/0.58  fof(f656,plain,(
% 1.72/0.58    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 1.72/0.58    inference(resolution,[],[f146,f69])).
% 1.72/0.58  fof(f146,plain,(
% 1.72/0.58    ( ! [X5] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X5)),X5)) )),
% 1.72/0.58    inference(resolution,[],[f134,f76])).
% 1.72/0.58  fof(f76,plain,(
% 1.72/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f37])).
% 1.72/0.58  fof(f37,plain,(
% 1.72/0.58    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.72/0.58    inference(ennf_transformation,[],[f7])).
% 1.72/0.58  fof(f7,axiom,(
% 1.72/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.72/0.58  fof(f708,plain,(
% 1.72/0.58    spl4_21),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f707])).
% 1.72/0.58  fof(f707,plain,(
% 1.72/0.58    $false | spl4_21),
% 1.72/0.58    inference(subsumption_resolution,[],[f706,f49])).
% 1.72/0.58  fof(f706,plain,(
% 1.72/0.58    ~v1_funct_1(sK3) | spl4_21),
% 1.72/0.58    inference(subsumption_resolution,[],[f705,f51])).
% 1.72/0.58  fof(f705,plain,(
% 1.72/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_21),
% 1.72/0.58    inference(subsumption_resolution,[],[f704,f146])).
% 1.72/0.58  fof(f704,plain,(
% 1.72/0.58    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_21),
% 1.72/0.58    inference(superposition,[],[f528,f57])).
% 1.72/0.58  fof(f528,plain,(
% 1.72/0.58    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_21),
% 1.72/0.58    inference(avatar_component_clause,[],[f526])).
% 1.72/0.58  fof(f526,plain,(
% 1.72/0.58    spl4_21 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.72/0.58  fof(f643,plain,(
% 1.72/0.58    spl4_20),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f642])).
% 1.72/0.58  fof(f642,plain,(
% 1.72/0.58    $false | spl4_20),
% 1.72/0.58    inference(subsumption_resolution,[],[f641,f49])).
% 1.72/0.58  fof(f641,plain,(
% 1.72/0.58    ~v1_funct_1(sK3) | spl4_20),
% 1.72/0.58    inference(subsumption_resolution,[],[f640,f51])).
% 1.72/0.58  fof(f640,plain,(
% 1.72/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_20),
% 1.72/0.58    inference(subsumption_resolution,[],[f639,f148])).
% 1.72/0.58  fof(f639,plain,(
% 1.72/0.58    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_20),
% 1.72/0.58    inference(superposition,[],[f524,f57])).
% 1.72/0.58  fof(f524,plain,(
% 1.72/0.58    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_20),
% 1.72/0.58    inference(avatar_component_clause,[],[f522])).
% 1.72/0.58  fof(f522,plain,(
% 1.72/0.58    spl4_20 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.72/0.58  fof(f533,plain,(
% 1.72/0.58    ~spl4_20 | ~spl4_21 | ~spl4_22 | spl4_3),
% 1.72/0.58    inference(avatar_split_clause,[],[f518,f97,f530,f526,f522])).
% 1.72/0.58  fof(f518,plain,(
% 1.72/0.58    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_3),
% 1.72/0.58    inference(resolution,[],[f99,f71])).
% 1.72/0.58  fof(f71,plain,(
% 1.72/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f35])).
% 1.72/0.58  fof(f35,plain,(
% 1.72/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.72/0.58    inference(flattening,[],[f34])).
% 1.72/0.58  fof(f34,plain,(
% 1.72/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.72/0.58    inference(ennf_transformation,[],[f13])).
% 1.72/0.58  fof(f13,axiom,(
% 1.72/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.72/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.72/0.58  fof(f99,plain,(
% 1.72/0.58    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.72/0.58    inference(avatar_component_clause,[],[f97])).
% 1.72/0.58  fof(f162,plain,(
% 1.72/0.58    spl4_1),
% 1.72/0.58    inference(avatar_contradiction_clause,[],[f161])).
% 1.72/0.58  fof(f161,plain,(
% 1.72/0.58    $false | spl4_1),
% 1.72/0.58    inference(subsumption_resolution,[],[f160,f49])).
% 1.72/0.58  fof(f160,plain,(
% 1.72/0.58    ~v1_funct_1(sK3) | spl4_1),
% 1.72/0.58    inference(subsumption_resolution,[],[f158,f51])).
% 1.72/0.58  fof(f158,plain,(
% 1.72/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_1),
% 1.72/0.58    inference(resolution,[],[f91,f55])).
% 1.72/0.58  fof(f55,plain,(
% 1.72/0.58    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.72/0.58    inference(cnf_transformation,[],[f23])).
% 1.72/0.58  fof(f91,plain,(
% 1.72/0.58    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.72/0.58    inference(avatar_component_clause,[],[f89])).
% 1.72/0.58  fof(f89,plain,(
% 1.72/0.58    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.72/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.72/0.58  fof(f109,plain,(
% 1.72/0.58    ~spl4_4 | spl4_5),
% 1.72/0.58    inference(avatar_split_clause,[],[f53,f106,f102])).
% 1.72/0.58  fof(f53,plain,(
% 1.72/0.58    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.72/0.58    inference(cnf_transformation,[],[f43])).
% 1.72/0.58  fof(f100,plain,(
% 1.72/0.58    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.72/0.58    inference(avatar_split_clause,[],[f54,f97,f93,f89])).
% 1.72/0.58  fof(f54,plain,(
% 1.72/0.58    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.72/0.58    inference(cnf_transformation,[],[f43])).
% 1.72/0.58  % SZS output end Proof for theBenchmark
% 1.72/0.58  % (5501)------------------------------
% 1.72/0.58  % (5501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (5501)Termination reason: Refutation
% 1.72/0.58  
% 1.72/0.58  % (5501)Memory used [KB]: 6908
% 1.72/0.58  % (5501)Time elapsed: 0.188 s
% 1.72/0.58  % (5501)------------------------------
% 1.72/0.58  % (5501)------------------------------
% 1.72/0.59  % (5476)Success in time 0.232 s
%------------------------------------------------------------------------------
