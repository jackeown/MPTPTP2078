%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 451 expanded)
%              Number of leaves         :   33 ( 148 expanded)
%              Depth                    :   18
%              Number of atoms          :  633 (2845 expanded)
%              Number of equality atoms :  121 ( 777 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1074,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f355,f397,f414,f466,f498,f512,f559,f563,f567,f692,f992,f1030,f1070])).

fof(f1070,plain,(
    ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f1069])).

fof(f1069,plain,
    ( $false
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1068,f101])).

fof(f101,plain,(
    v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f99,f67])).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f99,plain,
    ( v1_relat_1(sK7)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f65,f57])).

fof(f57,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( sK5 != k2_relset_1(sK4,sK5,sK7)
    & k1_xboole_0 != sK6
    & v2_funct_1(sK8)
    & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f18,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK5 != k2_relset_1(sK4,sK5,sK7)
          & k1_xboole_0 != sK6
          & v2_funct_1(X4)
          & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X4,sK5,sK6)
          & v1_funct_1(X4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( sK5 != k2_relset_1(sK4,sK5,sK7)
        & k1_xboole_0 != sK6
        & v2_funct_1(X4)
        & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X4,sK5,sK6)
        & v1_funct_1(X4) )
   => ( sK5 != k2_relset_1(sK4,sK5,sK7)
      & k1_xboole_0 != sK6
      & v2_funct_1(sK8)
      & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1068,plain,
    ( ~ v1_relat_1(sK7)
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1067,f112])).

fof(f112,plain,(
    v5_relat_1(sK7,sK5) ),
    inference(resolution,[],[f81,f57])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1067,plain,
    ( ~ v5_relat_1(sK7,sK5)
    | ~ v1_relat_1(sK7)
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1063,f147])).

fof(f147,plain,(
    sK5 != k2_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f136,f57])).

fof(f136,plain,
    ( sK5 != k2_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f64,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f64,plain,(
    sK5 != k2_relset_1(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f1063,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ v5_relat_1(sK7,sK5)
    | ~ v1_relat_1(sK7)
    | ~ spl9_24 ),
    inference(resolution,[],[f558,f109])).

fof(f109,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X2))
      | k2_relat_1(X2) = X1
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f76,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f76,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f558,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f556])).

fof(f556,plain,
    ( spl9_24
  <=> r1_tarski(sK5,k2_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f1030,plain,
    ( ~ spl9_14
    | ~ spl9_21
    | spl9_23
    | ~ spl9_25
    | ~ spl9_26
    | ~ spl9_59 ),
    inference(avatar_contradiction_clause,[],[f1029])).

fof(f1029,plain,
    ( $false
    | ~ spl9_14
    | ~ spl9_21
    | spl9_23
    | ~ spl9_25
    | ~ spl9_26
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f1028,f102])).

fof(f102,plain,(
    v1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f100,f67])).

fof(f100,plain,
    ( v1_relat_1(sK8)
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f45])).

fof(f1028,plain,
    ( ~ v1_relat_1(sK8)
    | ~ spl9_14
    | ~ spl9_21
    | spl9_23
    | ~ spl9_25
    | ~ spl9_26
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f1027,f58])).

fof(f58,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f1027,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_14
    | ~ spl9_21
    | spl9_23
    | ~ spl9_25
    | ~ spl9_26
    | ~ spl9_59 ),
    inference(subsumption_resolution,[],[f1025,f840])).

fof(f840,plain,
    ( ~ r1_tarski(sK6,k2_relat_1(sK8))
    | ~ spl9_14
    | ~ spl9_21
    | spl9_23
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f839,f537])).

fof(f537,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl9_21
  <=> v1_relat_1(k5_relat_1(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f839,plain,
    ( ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ r1_tarski(sK6,k2_relat_1(sK8))
    | ~ spl9_14
    | spl9_23
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f834,f353])).

fof(f353,plain,
    ( sK6 = k2_relat_1(k5_relat_1(sK7,sK8))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl9_14
  <=> sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f834,plain,
    ( sK6 != k2_relat_1(k5_relat_1(sK7,sK8))
    | ~ v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ r1_tarski(sK6,k2_relat_1(sK8))
    | spl9_23
    | ~ spl9_26 ),
    inference(resolution,[],[f601,f566])).

fof(f566,plain,
    ( ! [X1] :
        ( v5_relat_1(k5_relat_1(sK7,sK8),X1)
        | ~ r1_tarski(sK6,X1) )
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl9_26
  <=> ! [X1] :
        ( ~ r1_tarski(sK6,X1)
        | v5_relat_1(k5_relat_1(sK7,sK8),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f601,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(X0,k2_relat_1(sK8))
        | k2_relat_1(X0) != sK6
        | ~ v1_relat_1(X0) )
    | spl9_23 ),
    inference(subsumption_resolution,[],[f600,f113])).

fof(f113,plain,(
    v5_relat_1(sK8,sK6) ),
    inference(resolution,[],[f81,f60])).

fof(f600,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK6
        | ~ v5_relat_1(X0,k2_relat_1(sK8))
        | ~ v1_relat_1(X0)
        | ~ v5_relat_1(sK8,sK6) )
    | spl9_23 ),
    inference(inner_rewriting,[],[f599])).

fof(f599,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK6
        | ~ v5_relat_1(X0,k2_relat_1(sK8))
        | ~ v1_relat_1(X0)
        | ~ v5_relat_1(sK8,k2_relat_1(X0)) )
    | spl9_23 ),
    inference(subsumption_resolution,[],[f597,f102])).

fof(f597,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK6
        | ~ v5_relat_1(X0,k2_relat_1(sK8))
        | ~ v1_relat_1(X0)
        | ~ v5_relat_1(sK8,k2_relat_1(X0))
        | ~ v1_relat_1(sK8) )
    | spl9_23 ),
    inference(superposition,[],[f554,f159])).

fof(f159,plain,(
    ! [X2,X1] :
      ( k2_relat_1(X1) = k2_relat_1(X2)
      | ~ v5_relat_1(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X2,k2_relat_1(X1))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f109,f68])).

fof(f554,plain,
    ( sK6 != k2_relat_1(sK8)
    | spl9_23 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl9_23
  <=> sK6 = k2_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f1025,plain,
    ( r1_tarski(sK6,k2_relat_1(sK8))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_25
    | ~ spl9_59 ),
    inference(resolution,[],[f1022,f126])).

fof(f126,plain,(
    ! [X2] :
      ( sP0(k2_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f73,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f24,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f1022,plain,
    ( ! [X1] :
        ( ~ sP0(X1,sK8)
        | r1_tarski(sK6,X1) )
    | ~ spl9_25
    | ~ spl9_59 ),
    inference(resolution,[],[f1011,f562])).

fof(f562,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k5_relat_1(sK7,sK8),X0)
        | r1_tarski(sK6,X0) )
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl9_25
  <=> ! [X0] :
        ( r1_tarski(sK6,X0)
        | ~ v5_relat_1(k5_relat_1(sK7,sK8),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f1011,plain,
    ( ! [X0,X1] :
        ( v5_relat_1(k5_relat_1(sK7,X0),X1)
        | ~ sP0(X1,X0) )
    | ~ spl9_59 ),
    inference(resolution,[],[f984,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f984,plain,
    ( ! [X39,X37,X38] :
        ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | v5_relat_1(k5_relat_1(sK7,X37),X39) )
    | ~ spl9_59 ),
    inference(avatar_component_clause,[],[f983])).

fof(f983,plain,
    ( spl9_59
  <=> ! [X38,X37,X39] :
        ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | v5_relat_1(k5_relat_1(sK7,X37),X39) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f992,plain,(
    spl9_59 ),
    inference(avatar_split_clause,[],[f977,f983])).

fof(f977,plain,(
    ! [X35,X36,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v5_relat_1(k5_relat_1(sK7,X34),X36) ) ),
    inference(resolution,[],[f401,f57])).

fof(f401,plain,(
    ! [X14,X19,X17,X15,X18,X16] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v5_relat_1(k5_relat_1(X17,X14),X16) ) ),
    inference(resolution,[],[f262,f81])).

fof(f262,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f92,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f692,plain,
    ( spl9_21
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f661,f347,f536])).

fof(f347,plain,
    ( spl9_13
  <=> m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f661,plain,
    ( v1_relat_1(k5_relat_1(sK7,sK8))
    | ~ spl9_13 ),
    inference(resolution,[],[f348,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f348,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f347])).

fof(f567,plain,
    ( ~ spl9_21
    | spl9_26
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f527,f351,f565,f536])).

fof(f527,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK6,X1)
        | v5_relat_1(k5_relat_1(sK7,sK8),X1)
        | ~ v1_relat_1(k5_relat_1(sK7,sK8)) )
    | ~ spl9_14 ),
    inference(superposition,[],[f69,f353])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f563,plain,
    ( ~ spl9_21
    | spl9_25
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f526,f351,f561,f536])).

fof(f526,plain,
    ( ! [X0] :
        ( r1_tarski(sK6,X0)
        | ~ v5_relat_1(k5_relat_1(sK7,sK8),X0)
        | ~ v1_relat_1(k5_relat_1(sK7,sK8)) )
    | ~ spl9_14 ),
    inference(superposition,[],[f68,f353])).

fof(f559,plain,
    ( ~ spl9_23
    | spl9_24
    | ~ spl9_5
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f550,f351,f196,f556,f552])).

fof(f196,plain,
    ( spl9_5
  <=> sK5 = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f550,plain,
    ( r1_tarski(sK5,k2_relat_1(sK7))
    | sK6 != k2_relat_1(sK8)
    | ~ spl9_5
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f549,f198])).

fof(f198,plain,
    ( sK5 = k1_relat_1(sK8)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f196])).

fof(f549,plain,
    ( sK6 != k2_relat_1(sK8)
    | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7))
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f548,f102])).

fof(f548,plain,
    ( sK6 != k2_relat_1(sK8)
    | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7))
    | ~ v1_relat_1(sK8)
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f547,f58])).

fof(f547,plain,
    ( sK6 != k2_relat_1(sK8)
    | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f546,f101])).

fof(f546,plain,
    ( sK6 != k2_relat_1(sK8)
    | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f545,f55])).

fof(f55,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

% (6564)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f545,plain,
    ( sK6 != k2_relat_1(sK8)
    | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f525,f62])).

fof(f62,plain,(
    v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f525,plain,
    ( sK6 != k2_relat_1(sK8)
    | ~ v2_funct_1(sK8)
    | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_14 ),
    inference(superposition,[],[f66,f353])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

fof(f512,plain,(
    ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f60,f413])).

fof(f413,plain,
    ( ! [X0] : ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,sK6)))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl9_20
  <=> ! [X0] : ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f498,plain,(
    ~ spl9_19 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f57,f410])).

fof(f410,plain,
    ( ! [X1] : ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl9_19
  <=> ! [X1] : ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f466,plain,
    ( spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f465,f200,f196])).

fof(f200,plain,
    ( spl9_6
  <=> sP1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f465,plain,
    ( sP1(sK5,sK6)
    | sK5 = k1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f461,f59])).

fof(f59,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f461,plain,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | sP1(sK5,sK6)
    | sK5 = k1_relat_1(sK8) ),
    inference(resolution,[],[f60,f166])).

fof(f166,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f164,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f30,f41,f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f164,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f84,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f414,plain,
    ( spl9_19
    | spl9_20
    | spl9_13 ),
    inference(avatar_split_clause,[],[f398,f347,f412,f409])).

fof(f398,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,sK6)))
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) )
    | spl9_13 ),
    inference(resolution,[],[f262,f349])).

fof(f349,plain,
    ( ~ m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | spl9_13 ),
    inference(avatar_component_clause,[],[f347])).

fof(f397,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f395,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f45])).

fof(f395,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_6 ),
    inference(resolution,[],[f202,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

% (6569)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (6556)Refutation not found, incomplete strategy% (6556)------------------------------
% (6556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6556)Termination reason: Refutation not found, incomplete strategy

% (6556)Memory used [KB]: 10746
% (6556)Time elapsed: 0.130 s
% (6556)------------------------------
% (6556)------------------------------
% (6566)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (6550)Refutation not found, incomplete strategy% (6550)------------------------------
% (6550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6550)Termination reason: Refutation not found, incomplete strategy

% (6550)Memory used [KB]: 10746
% (6550)Time elapsed: 0.092 s
% (6550)------------------------------
% (6550)------------------------------
% (6561)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (6574)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (6572)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (6562)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f202,plain,
    ( sP1(sK5,sK6)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f200])).

fof(f355,plain,
    ( ~ spl9_13
    | spl9_14 ),
    inference(avatar_split_clause,[],[f345,f351,f347])).

fof(f345,plain,
    ( sK6 = k2_relat_1(k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(superposition,[],[f79,f343])).

fof(f343,plain,(
    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) ),
    inference(subsumption_resolution,[],[f342,f55])).

fof(f342,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f341,f57])).

fof(f341,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f340,f58])).

fof(f340,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f335,f60])).

fof(f335,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(superposition,[],[f61,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f61,plain,(
    sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:55:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (6554)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (6573)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (6571)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (6565)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (6568)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (6552)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (6567)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (6557)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (6559)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (6570)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (6558)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (6575)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (6551)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (6556)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (6560)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (6550)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (6563)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (6555)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (6553)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (6554)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1074,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f355,f397,f414,f466,f498,f512,f559,f563,f567,f692,f992,f1030,f1070])).
% 0.22/0.54  fof(f1070,plain,(
% 0.22/0.54    ~spl9_24),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1069])).
% 0.22/0.54  fof(f1069,plain,(
% 0.22/0.54    $false | ~spl9_24),
% 0.22/0.54    inference(subsumption_resolution,[],[f1068,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    v1_relat_1(sK7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f99,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    v1_relat_1(sK7) | ~v1_relat_1(k2_zfmisc_1(sK4,sK5))),
% 0.22/0.54    inference(resolution,[],[f65,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(sK8) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f18,f44,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(X4) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X4,sK5,sK6) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ? [X4] : (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(X4) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X4,sK5,sK6) & v1_funct_1(X4)) => (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(sK8) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.22/0.54    inference(negated_conjecture,[],[f15])).
% 0.22/0.54  fof(f15,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.54  fof(f1068,plain,(
% 0.22/0.54    ~v1_relat_1(sK7) | ~spl9_24),
% 0.22/0.54    inference(subsumption_resolution,[],[f1067,f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    v5_relat_1(sK7,sK5)),
% 0.22/0.54    inference(resolution,[],[f81,f57])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.54  fof(f1067,plain,(
% 0.22/0.54    ~v5_relat_1(sK7,sK5) | ~v1_relat_1(sK7) | ~spl9_24),
% 0.22/0.54    inference(subsumption_resolution,[],[f1063,f147])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    sK5 != k2_relat_1(sK7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f136,f57])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    sK5 != k2_relat_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 0.22/0.54    inference(superposition,[],[f64,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    sK5 != k2_relset_1(sK4,sK5,sK7)),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f1063,plain,(
% 0.22/0.54    sK5 = k2_relat_1(sK7) | ~v5_relat_1(sK7,sK5) | ~v1_relat_1(sK7) | ~spl9_24),
% 0.22/0.54    inference(resolution,[],[f558,f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(X2)) | k2_relat_1(X2) = X1 | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(resolution,[],[f76,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f558,plain,(
% 0.22/0.54    r1_tarski(sK5,k2_relat_1(sK7)) | ~spl9_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f556])).
% 0.22/0.54  fof(f556,plain,(
% 0.22/0.54    spl9_24 <=> r1_tarski(sK5,k2_relat_1(sK7))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.22/0.54  fof(f1030,plain,(
% 0.22/0.54    ~spl9_14 | ~spl9_21 | spl9_23 | ~spl9_25 | ~spl9_26 | ~spl9_59),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1029])).
% 0.22/0.54  fof(f1029,plain,(
% 0.22/0.54    $false | (~spl9_14 | ~spl9_21 | spl9_23 | ~spl9_25 | ~spl9_26 | ~spl9_59)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1028,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    v1_relat_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f100,f67])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    v1_relat_1(sK8) | ~v1_relat_1(k2_zfmisc_1(sK5,sK6))),
% 0.22/0.54    inference(resolution,[],[f65,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f1028,plain,(
% 0.22/0.54    ~v1_relat_1(sK8) | (~spl9_14 | ~spl9_21 | spl9_23 | ~spl9_25 | ~spl9_26 | ~spl9_59)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1027,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    v1_funct_1(sK8)),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f1027,plain,(
% 0.22/0.54    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_14 | ~spl9_21 | spl9_23 | ~spl9_25 | ~spl9_26 | ~spl9_59)),
% 0.22/0.54    inference(subsumption_resolution,[],[f1025,f840])).
% 0.22/0.54  fof(f840,plain,(
% 0.22/0.54    ~r1_tarski(sK6,k2_relat_1(sK8)) | (~spl9_14 | ~spl9_21 | spl9_23 | ~spl9_26)),
% 0.22/0.54    inference(subsumption_resolution,[],[f839,f537])).
% 0.22/0.54  fof(f537,plain,(
% 0.22/0.54    v1_relat_1(k5_relat_1(sK7,sK8)) | ~spl9_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f536])).
% 0.22/0.54  fof(f536,plain,(
% 0.22/0.54    spl9_21 <=> v1_relat_1(k5_relat_1(sK7,sK8))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.22/0.54  fof(f839,plain,(
% 0.22/0.54    ~v1_relat_1(k5_relat_1(sK7,sK8)) | ~r1_tarski(sK6,k2_relat_1(sK8)) | (~spl9_14 | spl9_23 | ~spl9_26)),
% 0.22/0.54    inference(subsumption_resolution,[],[f834,f353])).
% 0.22/0.54  fof(f353,plain,(
% 0.22/0.54    sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) | ~spl9_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f351])).
% 0.22/0.54  fof(f351,plain,(
% 0.22/0.54    spl9_14 <=> sK6 = k2_relat_1(k5_relat_1(sK7,sK8))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.54  fof(f834,plain,(
% 0.22/0.54    sK6 != k2_relat_1(k5_relat_1(sK7,sK8)) | ~v1_relat_1(k5_relat_1(sK7,sK8)) | ~r1_tarski(sK6,k2_relat_1(sK8)) | (spl9_23 | ~spl9_26)),
% 0.22/0.54    inference(resolution,[],[f601,f566])).
% 0.22/0.54  fof(f566,plain,(
% 0.22/0.54    ( ! [X1] : (v5_relat_1(k5_relat_1(sK7,sK8),X1) | ~r1_tarski(sK6,X1)) ) | ~spl9_26),
% 0.22/0.54    inference(avatar_component_clause,[],[f565])).
% 0.22/0.54  fof(f565,plain,(
% 0.22/0.54    spl9_26 <=> ! [X1] : (~r1_tarski(sK6,X1) | v5_relat_1(k5_relat_1(sK7,sK8),X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.22/0.54  fof(f601,plain,(
% 0.22/0.54    ( ! [X0] : (~v5_relat_1(X0,k2_relat_1(sK8)) | k2_relat_1(X0) != sK6 | ~v1_relat_1(X0)) ) | spl9_23),
% 0.22/0.54    inference(subsumption_resolution,[],[f600,f113])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    v5_relat_1(sK8,sK6)),
% 0.22/0.54    inference(resolution,[],[f81,f60])).
% 0.22/0.54  fof(f600,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(X0) != sK6 | ~v5_relat_1(X0,k2_relat_1(sK8)) | ~v1_relat_1(X0) | ~v5_relat_1(sK8,sK6)) ) | spl9_23),
% 0.22/0.54    inference(inner_rewriting,[],[f599])).
% 0.22/0.54  fof(f599,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(X0) != sK6 | ~v5_relat_1(X0,k2_relat_1(sK8)) | ~v1_relat_1(X0) | ~v5_relat_1(sK8,k2_relat_1(X0))) ) | spl9_23),
% 0.22/0.54    inference(subsumption_resolution,[],[f597,f102])).
% 0.22/0.54  fof(f597,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(X0) != sK6 | ~v5_relat_1(X0,k2_relat_1(sK8)) | ~v1_relat_1(X0) | ~v5_relat_1(sK8,k2_relat_1(X0)) | ~v1_relat_1(sK8)) ) | spl9_23),
% 0.22/0.54    inference(superposition,[],[f554,f159])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k2_relat_1(X1) = k2_relat_1(X2) | ~v5_relat_1(X1,k2_relat_1(X2)) | ~v1_relat_1(X1) | ~v5_relat_1(X2,k2_relat_1(X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(resolution,[],[f109,f68])).
% 0.22/0.54  fof(f554,plain,(
% 0.22/0.54    sK6 != k2_relat_1(sK8) | spl9_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f552])).
% 0.22/0.54  fof(f552,plain,(
% 0.22/0.54    spl9_23 <=> sK6 = k2_relat_1(sK8)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.22/0.54  fof(f1025,plain,(
% 0.22/0.54    r1_tarski(sK6,k2_relat_1(sK8)) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_25 | ~spl9_59)),
% 0.22/0.54    inference(resolution,[],[f1022,f126])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X2] : (sP0(k2_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(resolution,[],[f73,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f49])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(definition_folding,[],[f24,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.54  fof(f1022,plain,(
% 0.22/0.54    ( ! [X1] : (~sP0(X1,sK8) | r1_tarski(sK6,X1)) ) | (~spl9_25 | ~spl9_59)),
% 0.22/0.54    inference(resolution,[],[f1011,f562])).
% 0.22/0.54  fof(f562,plain,(
% 0.22/0.54    ( ! [X0] : (~v5_relat_1(k5_relat_1(sK7,sK8),X0) | r1_tarski(sK6,X0)) ) | ~spl9_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f561])).
% 0.22/0.54  fof(f561,plain,(
% 0.22/0.54    spl9_25 <=> ! [X0] : (r1_tarski(sK6,X0) | ~v5_relat_1(k5_relat_1(sK7,sK8),X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.22/0.54  fof(f1011,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v5_relat_1(k5_relat_1(sK7,X0),X1) | ~sP0(X1,X0)) ) | ~spl9_59),
% 0.22/0.54    inference(resolution,[],[f984,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f37])).
% 0.22/0.54  fof(f984,plain,(
% 0.22/0.54    ( ! [X39,X37,X38] : (~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) | v5_relat_1(k5_relat_1(sK7,X37),X39)) ) | ~spl9_59),
% 0.22/0.54    inference(avatar_component_clause,[],[f983])).
% 0.22/0.54  fof(f983,plain,(
% 0.22/0.54    spl9_59 <=> ! [X38,X37,X39] : (~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) | v5_relat_1(k5_relat_1(sK7,X37),X39))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 0.22/0.54  fof(f992,plain,(
% 0.22/0.54    spl9_59),
% 0.22/0.54    inference(avatar_split_clause,[],[f977,f983])).
% 0.22/0.54  fof(f977,plain,(
% 0.22/0.54    ( ! [X35,X36,X34] : (~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) | v5_relat_1(k5_relat_1(sK7,X34),X36)) )),
% 0.22/0.54    inference(resolution,[],[f401,f57])).
% 0.22/0.54  fof(f401,plain,(
% 0.22/0.54    ( ! [X14,X19,X17,X15,X18,X16] : (~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | v5_relat_1(k5_relat_1(X17,X14),X16)) )),
% 0.22/0.54    inference(resolution,[],[f262,f81])).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f261])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(superposition,[],[f92,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.22/0.54  fof(f692,plain,(
% 0.22/0.54    spl9_21 | ~spl9_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f661,f347,f536])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    spl9_13 <=> m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.54  fof(f661,plain,(
% 0.22/0.54    v1_relat_1(k5_relat_1(sK7,sK8)) | ~spl9_13),
% 0.22/0.54    inference(resolution,[],[f348,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f348,plain,(
% 0.22/0.54    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~spl9_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f347])).
% 0.22/0.54  fof(f567,plain,(
% 0.22/0.54    ~spl9_21 | spl9_26 | ~spl9_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f527,f351,f565,f536])).
% 0.22/0.54  fof(f527,plain,(
% 0.22/0.54    ( ! [X1] : (~r1_tarski(sK6,X1) | v5_relat_1(k5_relat_1(sK7,sK8),X1) | ~v1_relat_1(k5_relat_1(sK7,sK8))) ) | ~spl9_14),
% 0.22/0.54    inference(superposition,[],[f69,f353])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f46])).
% 0.22/0.54  fof(f563,plain,(
% 0.22/0.54    ~spl9_21 | spl9_25 | ~spl9_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f526,f351,f561,f536])).
% 0.22/0.54  fof(f526,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(sK6,X0) | ~v5_relat_1(k5_relat_1(sK7,sK8),X0) | ~v1_relat_1(k5_relat_1(sK7,sK8))) ) | ~spl9_14),
% 0.22/0.54    inference(superposition,[],[f68,f353])).
% 0.22/0.54  fof(f559,plain,(
% 0.22/0.54    ~spl9_23 | spl9_24 | ~spl9_5 | ~spl9_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f550,f351,f196,f556,f552])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    spl9_5 <=> sK5 = k1_relat_1(sK8)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.54  fof(f550,plain,(
% 0.22/0.54    r1_tarski(sK5,k2_relat_1(sK7)) | sK6 != k2_relat_1(sK8) | (~spl9_5 | ~spl9_14)),
% 0.22/0.54    inference(forward_demodulation,[],[f549,f198])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    sK5 = k1_relat_1(sK8) | ~spl9_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f196])).
% 0.22/0.54  fof(f549,plain,(
% 0.22/0.54    sK6 != k2_relat_1(sK8) | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7)) | ~spl9_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f548,f102])).
% 0.22/0.54  fof(f548,plain,(
% 0.22/0.54    sK6 != k2_relat_1(sK8) | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7)) | ~v1_relat_1(sK8) | ~spl9_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f547,f58])).
% 0.22/0.54  fof(f547,plain,(
% 0.22/0.54    sK6 != k2_relat_1(sK8) | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7)) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f546,f101])).
% 0.22/0.54  fof(f546,plain,(
% 0.22/0.54    sK6 != k2_relat_1(sK8) | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7)) | ~v1_relat_1(sK7) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f545,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    v1_funct_1(sK7)),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  % (6564)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  fof(f545,plain,(
% 0.22/0.54    sK6 != k2_relat_1(sK8) | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_14),
% 0.22/0.54    inference(subsumption_resolution,[],[f525,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    v2_funct_1(sK8)),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f525,plain,(
% 0.22/0.54    sK6 != k2_relat_1(sK8) | ~v2_funct_1(sK8) | r1_tarski(k1_relat_1(sK8),k2_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_14),
% 0.22/0.54    inference(superposition,[],[f66,f353])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) | ~v2_funct_1(X0) | r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).
% 0.22/0.54  fof(f512,plain,(
% 0.22/0.54    ~spl9_20),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f509])).
% 0.22/0.54  fof(f509,plain,(
% 0.22/0.54    $false | ~spl9_20),
% 0.22/0.54    inference(subsumption_resolution,[],[f60,f413])).
% 0.22/0.54  fof(f413,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,sK6)))) ) | ~spl9_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f412])).
% 0.22/0.54  fof(f412,plain,(
% 0.22/0.54    spl9_20 <=> ! [X0] : ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,sK6)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.22/0.54  fof(f498,plain,(
% 0.22/0.54    ~spl9_19),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f497])).
% 0.22/0.54  fof(f497,plain,(
% 0.22/0.54    $false | ~spl9_19),
% 0.22/0.54    inference(subsumption_resolution,[],[f57,f410])).
% 0.22/0.54  fof(f410,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))) ) | ~spl9_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f409])).
% 0.22/0.54  fof(f409,plain,(
% 0.22/0.54    spl9_19 <=> ! [X1] : ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.54  fof(f466,plain,(
% 0.22/0.54    spl9_5 | spl9_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f465,f200,f196])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    spl9_6 <=> sP1(sK5,sK6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.54  fof(f465,plain,(
% 0.22/0.54    sP1(sK5,sK6) | sK5 = k1_relat_1(sK8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f461,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    v1_funct_2(sK8,sK5,sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f461,plain,(
% 0.22/0.54    ~v1_funct_2(sK8,sK5,sK6) | sP1(sK5,sK6) | sK5 = k1_relat_1(sK8)),
% 0.22/0.54    inference(resolution,[],[f60,f166])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f164,f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(definition_folding,[],[f30,f41,f40,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.54    inference(superposition,[],[f84,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.22/0.54    inference(rectify,[],[f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f40])).
% 0.22/0.54  fof(f414,plain,(
% 0.22/0.54    spl9_19 | spl9_20 | spl9_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f398,f347,f412,f409])).
% 0.22/0.54  fof(f398,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,sK6))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))) ) | spl9_13),
% 0.22/0.54    inference(resolution,[],[f262,f349])).
% 0.22/0.54  fof(f349,plain,(
% 0.22/0.54    ~m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | spl9_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f347])).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    ~spl9_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f396])).
% 0.22/0.54  fof(f396,plain,(
% 0.22/0.54    $false | ~spl9_6),
% 0.22/0.54    inference(subsumption_resolution,[],[f395,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    k1_xboole_0 != sK6),
% 0.22/0.54    inference(cnf_transformation,[],[f45])).
% 0.22/0.54  fof(f395,plain,(
% 0.22/0.54    k1_xboole_0 = sK6 | ~spl9_6),
% 0.22/0.54    inference(resolution,[],[f202,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f39])).
% 0.22/0.54  % (6569)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (6556)Refutation not found, incomplete strategy% (6556)------------------------------
% 0.22/0.54  % (6556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6556)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (6556)Memory used [KB]: 10746
% 0.22/0.54  % (6556)Time elapsed: 0.130 s
% 0.22/0.54  % (6556)------------------------------
% 0.22/0.54  % (6556)------------------------------
% 0.22/0.54  % (6566)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (6550)Refutation not found, incomplete strategy% (6550)------------------------------
% 0.22/0.54  % (6550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6550)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (6550)Memory used [KB]: 10746
% 0.22/0.54  % (6550)Time elapsed: 0.092 s
% 0.22/0.54  % (6550)------------------------------
% 0.22/0.54  % (6550)------------------------------
% 0.22/0.55  % (6561)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (6574)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.55  % (6572)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.55  % (6562)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    sP1(sK5,sK6) | ~spl9_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f200])).
% 0.22/0.56  fof(f355,plain,(
% 0.22/0.56    ~spl9_13 | spl9_14),
% 0.22/0.56    inference(avatar_split_clause,[],[f345,f351,f347])).
% 0.22/0.56  fof(f345,plain,(
% 0.22/0.56    sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) | ~m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 0.22/0.56    inference(superposition,[],[f79,f343])).
% 0.22/0.56  fof(f343,plain,(
% 0.22/0.56    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))),
% 0.22/0.56    inference(subsumption_resolution,[],[f342,f55])).
% 0.22/0.56  fof(f342,plain,(
% 0.22/0.56    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~v1_funct_1(sK7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f341,f57])).
% 0.22/0.56  fof(f341,plain,(
% 0.22/0.56    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f340,f58])).
% 0.22/0.56  fof(f340,plain,(
% 0.22/0.56    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f335,f60])).
% 0.22/0.56  fof(f335,plain,(
% 0.22/0.56    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 0.22/0.56    inference(superposition,[],[f61,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.56    inference(flattening,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (6554)------------------------------
% 0.22/0.56  % (6554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6554)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (6554)Memory used [KB]: 6652
% 0.22/0.56  % (6554)Time elapsed: 0.123 s
% 0.22/0.56  % (6554)------------------------------
% 0.22/0.56  % (6554)------------------------------
% 0.22/0.56  % (6549)Success in time 0.195 s
%------------------------------------------------------------------------------
