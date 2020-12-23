%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:19 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 611 expanded)
%              Number of leaves         :   20 ( 152 expanded)
%              Depth                    :   16
%              Number of atoms          :  429 (3636 expanded)
%              Number of equality atoms :  118 ( 917 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f454,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f108,f176,f290,f319,f437,f453])).

fof(f453,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f451,f355])).

fof(f355,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f346,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f346,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl4_4 ),
    inference(superposition,[],[f48,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f48,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f40])).

fof(f40,plain,
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f451,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f450,f374])).

fof(f374,plain,
    ( sK3 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f174,f107])).

fof(f174,plain,(
    sK3 = k7_relat_1(sK3,sK0) ),
    inference(subsumption_resolution,[],[f173,f127])).

fof(f127,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f126,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f126,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f53,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f173,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f140,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f140,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f66,f49])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f450,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f449,f414])).

fof(f414,plain,
    ( ! [X8,X9] : k2_partfun1(X8,k1_xboole_0,sK3,X9) = k7_relat_1(sK3,X9)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f406,f47])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f406,plain,
    ( ! [X8,X9] :
        ( k2_partfun1(X8,k1_xboole_0,sK3,X9) = k7_relat_1(sK3,X9)
        | ~ v1_funct_1(sK3) )
    | ~ spl4_4 ),
    inference(resolution,[],[f356,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k2_partfun1(X0,k1_xboole_0,X1,X2) = k7_relat_1(X1,X2)
      | ~ v1_funct_1(X1) ) ),
    inference(superposition,[],[f75,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f356,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f347,f80])).

fof(f347,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f49,f102])).

fof(f449,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f448,f388])).

fof(f388,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5 ),
    inference(resolution,[],[f366,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f366,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f50,f107])).

fof(f50,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f448,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f94,f102])).

fof(f94,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f437,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f435,f360])).

fof(f360,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f351,f80])).

fof(f351,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4 ),
    inference(superposition,[],[f164,f102])).

fof(f164,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f163,f159])).

fof(f159,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(subsumption_resolution,[],[f156,f47])).

fof(f156,plain,(
    ! [X0] :
      ( k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f75,f49])).

fof(f163,plain,(
    ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f160,f47])).

fof(f160,plain,(
    ! [X0] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f77,f49])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f435,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f425,f359])).

fof(f359,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,X0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f350,f107])).

fof(f350,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,k1_xboole_0,sK3,X0)
    | ~ spl4_4 ),
    inference(superposition,[],[f159,f102])).

fof(f425,plain,
    ( ~ m1_subset_1(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f341,f388])).

fof(f341,plain,
    ( ~ m1_subset_1(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f340,f107])).

fof(f340,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f339,f80])).

fof(f339,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f98,f102])).

fof(f98,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f319,plain,
    ( spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f316,f193])).

fof(f193,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(superposition,[],[f94,f159])).

fof(f316,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_4 ),
    inference(superposition,[],[f251,f237])).

fof(f237,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_4 ),
    inference(resolution,[],[f197,f50])).

fof(f197,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK0)
        | k1_relat_1(k7_relat_1(sK3,X3)) = X3 )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f196,f127])).

fof(f196,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK0)
        | k1_relat_1(k7_relat_1(sK3,X3)) = X3
        | ~ v1_relat_1(sK3) )
    | spl4_4 ),
    inference(superposition,[],[f57,f177])).

fof(f177,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f146,f169])).

fof(f169,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f168,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f168,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f165,f48])).

fof(f165,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f146,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f251,plain,
    ( ! [X3] : v1_funct_2(k7_relat_1(sK3,X3),k1_relat_1(k7_relat_1(sK3,X3)),sK1)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f250,f103])).

fof(f250,plain,(
    ! [X3] :
      ( k1_xboole_0 = sK1
      | v1_funct_2(k7_relat_1(sK3,X3),k1_relat_1(k7_relat_1(sK3,X3)),sK1) ) ),
    inference(subsumption_resolution,[],[f243,f240])).

fof(f240,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK3,X0)) = k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f222,f65])).

fof(f222,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) ),
    inference(resolution,[],[f155,f164])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) ) ),
    inference(resolution,[],[f74,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f243,plain,(
    ! [X3] :
      ( k1_relat_1(k7_relat_1(sK3,X3)) != k1_relset_1(k1_relat_1(k7_relat_1(sK3,X3)),sK1,k7_relat_1(sK3,X3))
      | k1_xboole_0 = sK1
      | v1_funct_2(k7_relat_1(sK3,X3),k1_relat_1(k7_relat_1(sK3,X3)),sK1) ) ),
    inference(resolution,[],[f222,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f290,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f286,f192])).

fof(f192,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(superposition,[],[f98,f159])).

fof(f286,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_4 ),
    inference(superposition,[],[f222,f237])).

fof(f176,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f152,f90])).

fof(f90,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f152,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f149,f47])).

fof(f149,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f51,f105,f101])).

fof(f51,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f52,f96,f92,f88])).

fof(f52,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (694)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (686)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (691)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (684)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (687)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (672)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (678)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.56  % (679)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (676)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (675)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.56  % (681)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.56  % (689)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.57  % (683)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.42/0.57  % (695)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.42/0.57  % (692)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.42/0.58  % (688)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.42/0.58  % (680)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.42/0.58  % (671)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.42/0.58  % (674)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.42/0.59  % (690)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.42/0.59  % (677)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.75/0.59  % (685)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.75/0.59  % (670)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.75/0.59  % (682)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.75/0.60  % (680)Refutation found. Thanks to Tanya!
% 1.75/0.60  % SZS status Theorem for theBenchmark
% 1.75/0.60  % (693)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.75/0.60  % (669)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.75/0.61  % SZS output start Proof for theBenchmark
% 1.75/0.61  fof(f454,plain,(
% 1.75/0.61    $false),
% 1.75/0.61    inference(avatar_sat_refutation,[],[f99,f108,f176,f290,f319,f437,f453])).
% 1.75/0.61  fof(f453,plain,(
% 1.75/0.61    spl4_2 | ~spl4_4 | ~spl4_5),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f452])).
% 1.75/0.61  fof(f452,plain,(
% 1.75/0.61    $false | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(subsumption_resolution,[],[f451,f355])).
% 1.75/0.61  fof(f355,plain,(
% 1.75/0.61    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(forward_demodulation,[],[f346,f107])).
% 1.75/0.61  fof(f107,plain,(
% 1.75/0.61    k1_xboole_0 = sK0 | ~spl4_5),
% 1.75/0.61    inference(avatar_component_clause,[],[f105])).
% 1.75/0.61  fof(f105,plain,(
% 1.75/0.61    spl4_5 <=> k1_xboole_0 = sK0),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.75/0.61  fof(f346,plain,(
% 1.75/0.61    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl4_4),
% 1.75/0.61    inference(superposition,[],[f48,f102])).
% 1.75/0.61  fof(f102,plain,(
% 1.75/0.61    k1_xboole_0 = sK1 | ~spl4_4),
% 1.75/0.61    inference(avatar_component_clause,[],[f101])).
% 1.75/0.61  fof(f101,plain,(
% 1.75/0.61    spl4_4 <=> k1_xboole_0 = sK1),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.75/0.61  fof(f48,plain,(
% 1.75/0.61    v1_funct_2(sK3,sK0,sK1)),
% 1.75/0.61    inference(cnf_transformation,[],[f41])).
% 1.75/0.61  fof(f41,plain,(
% 1.75/0.61    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.75/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f40])).
% 1.75/0.61  fof(f40,plain,(
% 1.75/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.75/0.61    introduced(choice_axiom,[])).
% 1.75/0.61  fof(f20,plain,(
% 1.75/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.75/0.61    inference(flattening,[],[f19])).
% 1.75/0.61  fof(f19,plain,(
% 1.75/0.61    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.75/0.61    inference(ennf_transformation,[],[f17])).
% 1.75/0.61  fof(f17,negated_conjecture,(
% 1.75/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.75/0.61    inference(negated_conjecture,[],[f16])).
% 1.75/0.61  fof(f16,conjecture,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 1.75/0.61  fof(f451,plain,(
% 1.75/0.61    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(forward_demodulation,[],[f450,f374])).
% 1.75/0.61  fof(f374,plain,(
% 1.75/0.61    sK3 = k7_relat_1(sK3,k1_xboole_0) | ~spl4_5),
% 1.75/0.61    inference(superposition,[],[f174,f107])).
% 1.75/0.61  fof(f174,plain,(
% 1.75/0.61    sK3 = k7_relat_1(sK3,sK0)),
% 1.75/0.61    inference(subsumption_resolution,[],[f173,f127])).
% 1.75/0.61  fof(f127,plain,(
% 1.75/0.61    v1_relat_1(sK3)),
% 1.75/0.61    inference(subsumption_resolution,[],[f126,f55])).
% 1.75/0.61  fof(f55,plain,(
% 1.75/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f5])).
% 1.75/0.61  fof(f5,axiom,(
% 1.75/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.75/0.61  fof(f126,plain,(
% 1.75/0.61    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.75/0.61    inference(resolution,[],[f53,f49])).
% 1.75/0.61  fof(f49,plain,(
% 1.75/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.61    inference(cnf_transformation,[],[f41])).
% 1.75/0.61  fof(f53,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f21])).
% 1.75/0.61  fof(f21,plain,(
% 1.75/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.75/0.61    inference(ennf_transformation,[],[f4])).
% 1.75/0.61  fof(f4,axiom,(
% 1.75/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.75/0.61  fof(f173,plain,(
% 1.75/0.61    sK3 = k7_relat_1(sK3,sK0) | ~v1_relat_1(sK3)),
% 1.75/0.61    inference(resolution,[],[f140,f58])).
% 1.75/0.61  fof(f58,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f27])).
% 1.75/0.61  fof(f27,plain,(
% 1.75/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.75/0.61    inference(flattening,[],[f26])).
% 1.75/0.61  fof(f26,plain,(
% 1.75/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.75/0.61    inference(ennf_transformation,[],[f6])).
% 1.75/0.61  fof(f6,axiom,(
% 1.75/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.75/0.61  fof(f140,plain,(
% 1.75/0.61    v4_relat_1(sK3,sK0)),
% 1.75/0.61    inference(resolution,[],[f66,f49])).
% 1.75/0.61  fof(f66,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f29])).
% 1.75/0.61  fof(f29,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.61    inference(ennf_transformation,[],[f18])).
% 1.75/0.61  fof(f18,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.75/0.61    inference(pure_predicate_removal,[],[f9])).
% 1.75/0.61  fof(f9,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.75/0.61  fof(f450,plain,(
% 1.75/0.61    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(forward_demodulation,[],[f449,f414])).
% 1.75/0.61  fof(f414,plain,(
% 1.75/0.61    ( ! [X8,X9] : (k2_partfun1(X8,k1_xboole_0,sK3,X9) = k7_relat_1(sK3,X9)) ) | ~spl4_4),
% 1.75/0.61    inference(subsumption_resolution,[],[f406,f47])).
% 1.75/0.61  fof(f47,plain,(
% 1.75/0.61    v1_funct_1(sK3)),
% 1.75/0.61    inference(cnf_transformation,[],[f41])).
% 1.75/0.61  fof(f406,plain,(
% 1.75/0.61    ( ! [X8,X9] : (k2_partfun1(X8,k1_xboole_0,sK3,X9) = k7_relat_1(sK3,X9) | ~v1_funct_1(sK3)) ) | ~spl4_4),
% 1.75/0.61    inference(resolution,[],[f356,f157])).
% 1.75/0.61  fof(f157,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k2_partfun1(X0,k1_xboole_0,X1,X2) = k7_relat_1(X1,X2) | ~v1_funct_1(X1)) )),
% 1.75/0.61    inference(superposition,[],[f75,f80])).
% 1.75/0.61  fof(f80,plain,(
% 1.75/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.75/0.61    inference(equality_resolution,[],[f64])).
% 1.75/0.61  fof(f64,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.75/0.61    inference(cnf_transformation,[],[f45])).
% 1.75/0.61  fof(f45,plain,(
% 1.75/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.75/0.61    inference(flattening,[],[f44])).
% 1.75/0.61  fof(f44,plain,(
% 1.75/0.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.75/0.61    inference(nnf_transformation,[],[f3])).
% 1.75/0.61  fof(f3,axiom,(
% 1.75/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.75/0.61  fof(f75,plain,(
% 1.75/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f37])).
% 1.75/0.61  fof(f37,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.75/0.61    inference(flattening,[],[f36])).
% 1.75/0.61  fof(f36,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.75/0.61    inference(ennf_transformation,[],[f15])).
% 1.75/0.61  fof(f15,axiom,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.75/0.61  fof(f356,plain,(
% 1.75/0.61    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_4),
% 1.75/0.61    inference(forward_demodulation,[],[f347,f80])).
% 1.75/0.61  fof(f347,plain,(
% 1.75/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl4_4),
% 1.75/0.61    inference(superposition,[],[f49,f102])).
% 1.75/0.61  fof(f449,plain,(
% 1.75/0.61    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(forward_demodulation,[],[f448,f388])).
% 1.75/0.61  fof(f388,plain,(
% 1.75/0.61    k1_xboole_0 = sK2 | ~spl4_5),
% 1.75/0.61    inference(resolution,[],[f366,f54])).
% 1.75/0.61  fof(f54,plain,(
% 1.75/0.61    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f22,plain,(
% 1.75/0.61    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.75/0.61    inference(ennf_transformation,[],[f2])).
% 1.75/0.61  fof(f2,axiom,(
% 1.75/0.61    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.75/0.61  fof(f366,plain,(
% 1.75/0.61    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 1.75/0.61    inference(superposition,[],[f50,f107])).
% 1.75/0.61  fof(f50,plain,(
% 1.75/0.61    r1_tarski(sK2,sK0)),
% 1.75/0.61    inference(cnf_transformation,[],[f41])).
% 1.75/0.61  fof(f448,plain,(
% 1.75/0.61    ~v1_funct_2(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 1.75/0.61    inference(forward_demodulation,[],[f94,f102])).
% 1.75/0.61  fof(f94,plain,(
% 1.75/0.61    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 1.75/0.61    inference(avatar_component_clause,[],[f92])).
% 1.75/0.61  fof(f92,plain,(
% 1.75/0.61    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.75/0.61  fof(f437,plain,(
% 1.75/0.61    spl4_3 | ~spl4_4 | ~spl4_5),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f436])).
% 1.75/0.61  fof(f436,plain,(
% 1.75/0.61    $false | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(subsumption_resolution,[],[f435,f360])).
% 1.75/0.61  fof(f360,plain,(
% 1.75/0.61    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_4),
% 1.75/0.61    inference(forward_demodulation,[],[f351,f80])).
% 1.75/0.61  fof(f351,plain,(
% 1.75/0.61    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))) ) | ~spl4_4),
% 1.75/0.61    inference(superposition,[],[f164,f102])).
% 1.75/0.61  fof(f164,plain,(
% 1.75/0.61    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.75/0.61    inference(forward_demodulation,[],[f163,f159])).
% 1.75/0.61  fof(f159,plain,(
% 1.75/0.61    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) )),
% 1.75/0.61    inference(subsumption_resolution,[],[f156,f47])).
% 1.75/0.61  fof(f156,plain,(
% 1.75/0.61    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) | ~v1_funct_1(sK3)) )),
% 1.75/0.61    inference(resolution,[],[f75,f49])).
% 1.75/0.61  fof(f163,plain,(
% 1.75/0.61    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.75/0.61    inference(subsumption_resolution,[],[f160,f47])).
% 1.75/0.61  fof(f160,plain,(
% 1.75/0.61    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 1.75/0.61    inference(resolution,[],[f77,f49])).
% 1.75/0.61  fof(f77,plain,(
% 1.75/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f39])).
% 1.75/0.61  fof(f39,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.75/0.61    inference(flattening,[],[f38])).
% 1.75/0.61  fof(f38,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.75/0.61    inference(ennf_transformation,[],[f14])).
% 1.75/0.61  fof(f14,axiom,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.75/0.61  fof(f435,plain,(
% 1.75/0.61    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(forward_demodulation,[],[f425,f359])).
% 1.75/0.61  fof(f359,plain,(
% 1.75/0.61    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,X0)) ) | (~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(forward_demodulation,[],[f350,f107])).
% 1.75/0.61  fof(f350,plain,(
% 1.75/0.61    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,k1_xboole_0,sK3,X0)) ) | ~spl4_4),
% 1.75/0.61    inference(superposition,[],[f159,f102])).
% 1.75/0.61  fof(f425,plain,(
% 1.75/0.61    ~m1_subset_1(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(superposition,[],[f341,f388])).
% 1.75/0.61  fof(f341,plain,(
% 1.75/0.61    ~m1_subset_1(k2_partfun1(k1_xboole_0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4 | ~spl4_5)),
% 1.75/0.61    inference(forward_demodulation,[],[f340,f107])).
% 1.75/0.61  fof(f340,plain,(
% 1.75/0.61    ~m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_4)),
% 1.75/0.61    inference(forward_demodulation,[],[f339,f80])).
% 1.75/0.61  fof(f339,plain,(
% 1.75/0.61    ~m1_subset_1(k2_partfun1(sK0,k1_xboole_0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) | (spl4_3 | ~spl4_4)),
% 1.75/0.61    inference(forward_demodulation,[],[f98,f102])).
% 1.75/0.61  fof(f98,plain,(
% 1.75/0.61    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.75/0.61    inference(avatar_component_clause,[],[f96])).
% 1.75/0.61  fof(f96,plain,(
% 1.75/0.61    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.75/0.61  fof(f319,plain,(
% 1.75/0.61    spl4_2 | spl4_4),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f318])).
% 1.75/0.61  fof(f318,plain,(
% 1.75/0.61    $false | (spl4_2 | spl4_4)),
% 1.75/0.61    inference(subsumption_resolution,[],[f316,f193])).
% 1.75/0.61  fof(f193,plain,(
% 1.75/0.61    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 1.75/0.61    inference(superposition,[],[f94,f159])).
% 1.75/0.61  fof(f316,plain,(
% 1.75/0.61    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_4),
% 1.75/0.61    inference(superposition,[],[f251,f237])).
% 1.75/0.61  fof(f237,plain,(
% 1.75/0.61    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_4),
% 1.75/0.61    inference(resolution,[],[f197,f50])).
% 1.75/0.61  fof(f197,plain,(
% 1.75/0.61    ( ! [X3] : (~r1_tarski(X3,sK0) | k1_relat_1(k7_relat_1(sK3,X3)) = X3) ) | spl4_4),
% 1.75/0.61    inference(subsumption_resolution,[],[f196,f127])).
% 1.75/0.61  fof(f196,plain,(
% 1.75/0.61    ( ! [X3] : (~r1_tarski(X3,sK0) | k1_relat_1(k7_relat_1(sK3,X3)) = X3 | ~v1_relat_1(sK3)) ) | spl4_4),
% 1.75/0.61    inference(superposition,[],[f57,f177])).
% 1.75/0.61  fof(f177,plain,(
% 1.75/0.61    sK0 = k1_relat_1(sK3) | spl4_4),
% 1.75/0.61    inference(superposition,[],[f146,f169])).
% 1.75/0.61  fof(f169,plain,(
% 1.75/0.61    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 1.75/0.61    inference(subsumption_resolution,[],[f168,f103])).
% 1.75/0.61  fof(f103,plain,(
% 1.75/0.61    k1_xboole_0 != sK1 | spl4_4),
% 1.75/0.61    inference(avatar_component_clause,[],[f101])).
% 1.75/0.61  fof(f168,plain,(
% 1.75/0.61    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.75/0.61    inference(subsumption_resolution,[],[f165,f48])).
% 1.75/0.61  fof(f165,plain,(
% 1.75/0.61    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.75/0.61    inference(resolution,[],[f67,f49])).
% 1.75/0.61  fof(f67,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.75/0.61    inference(cnf_transformation,[],[f46])).
% 1.75/0.61  fof(f46,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.61    inference(nnf_transformation,[],[f31])).
% 1.75/0.61  fof(f31,plain,(
% 1.75/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.61    inference(flattening,[],[f30])).
% 1.75/0.61  fof(f30,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.61    inference(ennf_transformation,[],[f13])).
% 1.75/0.61  fof(f13,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.75/0.61  fof(f146,plain,(
% 1.75/0.61    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.75/0.61    inference(resolution,[],[f65,f49])).
% 1.75/0.61  fof(f65,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f28])).
% 1.75/0.61  fof(f28,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.61    inference(ennf_transformation,[],[f10])).
% 1.75/0.61  fof(f10,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.75/0.61  fof(f57,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f25])).
% 1.75/0.61  fof(f25,plain,(
% 1.75/0.61    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.75/0.61    inference(flattening,[],[f24])).
% 1.75/0.61  fof(f24,plain,(
% 1.75/0.61    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.75/0.61    inference(ennf_transformation,[],[f8])).
% 1.75/0.61  fof(f8,axiom,(
% 1.75/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.75/0.61  fof(f251,plain,(
% 1.75/0.61    ( ! [X3] : (v1_funct_2(k7_relat_1(sK3,X3),k1_relat_1(k7_relat_1(sK3,X3)),sK1)) ) | spl4_4),
% 1.75/0.61    inference(subsumption_resolution,[],[f250,f103])).
% 1.75/0.61  fof(f250,plain,(
% 1.75/0.61    ( ! [X3] : (k1_xboole_0 = sK1 | v1_funct_2(k7_relat_1(sK3,X3),k1_relat_1(k7_relat_1(sK3,X3)),sK1)) )),
% 1.75/0.61    inference(subsumption_resolution,[],[f243,f240])).
% 1.75/0.61  fof(f240,plain,(
% 1.75/0.61    ( ! [X0] : (k1_relat_1(k7_relat_1(sK3,X0)) = k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0))) )),
% 1.75/0.61    inference(resolution,[],[f222,f65])).
% 1.75/0.61  fof(f222,plain,(
% 1.75/0.61    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))) )),
% 1.75/0.61    inference(resolution,[],[f155,f164])).
% 1.75/0.61  fof(f155,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))) )),
% 1.75/0.61    inference(resolution,[],[f74,f78])).
% 1.75/0.61  fof(f78,plain,(
% 1.75/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.75/0.61    inference(equality_resolution,[],[f60])).
% 1.75/0.61  fof(f60,plain,(
% 1.75/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.75/0.61    inference(cnf_transformation,[],[f43])).
% 1.75/0.61  fof(f43,plain,(
% 1.75/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.61    inference(flattening,[],[f42])).
% 1.75/0.61  fof(f42,plain,(
% 1.75/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.61    inference(nnf_transformation,[],[f1])).
% 1.75/0.61  fof(f1,axiom,(
% 1.75/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.75/0.61  fof(f74,plain,(
% 1.75/0.61    ( ! [X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f35])).
% 1.75/0.61  fof(f35,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.75/0.61    inference(flattening,[],[f34])).
% 1.75/0.61  fof(f34,plain,(
% 1.75/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 1.75/0.61    inference(ennf_transformation,[],[f11])).
% 1.75/0.61  fof(f11,axiom,(
% 1.75/0.61    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 1.75/0.61  fof(f243,plain,(
% 1.75/0.61    ( ! [X3] : (k1_relat_1(k7_relat_1(sK3,X3)) != k1_relset_1(k1_relat_1(k7_relat_1(sK3,X3)),sK1,k7_relat_1(sK3,X3)) | k1_xboole_0 = sK1 | v1_funct_2(k7_relat_1(sK3,X3),k1_relat_1(k7_relat_1(sK3,X3)),sK1)) )),
% 1.75/0.61    inference(resolution,[],[f222,f69])).
% 1.75/0.61  fof(f69,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f46])).
% 1.75/0.61  fof(f290,plain,(
% 1.75/0.61    spl4_3 | spl4_4),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f289])).
% 1.75/0.61  fof(f289,plain,(
% 1.75/0.61    $false | (spl4_3 | spl4_4)),
% 1.75/0.61    inference(subsumption_resolution,[],[f286,f192])).
% 1.75/0.61  fof(f192,plain,(
% 1.75/0.61    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 1.75/0.61    inference(superposition,[],[f98,f159])).
% 1.75/0.61  fof(f286,plain,(
% 1.75/0.61    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_4),
% 1.75/0.61    inference(superposition,[],[f222,f237])).
% 1.75/0.61  fof(f176,plain,(
% 1.75/0.61    spl4_1),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f175])).
% 1.75/0.61  fof(f175,plain,(
% 1.75/0.61    $false | spl4_1),
% 1.75/0.61    inference(resolution,[],[f152,f90])).
% 1.75/0.61  fof(f90,plain,(
% 1.75/0.61    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 1.75/0.61    inference(avatar_component_clause,[],[f88])).
% 1.75/0.61  fof(f88,plain,(
% 1.75/0.61    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.75/0.61  fof(f152,plain,(
% 1.75/0.61    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 1.75/0.61    inference(subsumption_resolution,[],[f149,f47])).
% 1.75/0.61  fof(f149,plain,(
% 1.75/0.61    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 1.75/0.61    inference(resolution,[],[f76,f49])).
% 1.75/0.61  fof(f76,plain,(
% 1.75/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~v1_funct_1(X2)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f39])).
% 1.75/0.61  fof(f108,plain,(
% 1.75/0.61    ~spl4_4 | spl4_5),
% 1.75/0.61    inference(avatar_split_clause,[],[f51,f105,f101])).
% 1.75/0.61  fof(f51,plain,(
% 1.75/0.61    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.75/0.61    inference(cnf_transformation,[],[f41])).
% 1.75/0.61  fof(f99,plain,(
% 1.75/0.61    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.75/0.61    inference(avatar_split_clause,[],[f52,f96,f92,f88])).
% 1.75/0.61  fof(f52,plain,(
% 1.75/0.61    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.75/0.61    inference(cnf_transformation,[],[f41])).
% 1.75/0.61  % SZS output end Proof for theBenchmark
% 1.75/0.61  % (680)------------------------------
% 1.75/0.61  % (680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.61  % (680)Termination reason: Refutation
% 1.75/0.61  
% 1.75/0.61  % (680)Memory used [KB]: 10874
% 1.75/0.61  % (680)Time elapsed: 0.108 s
% 1.75/0.61  % (680)------------------------------
% 1.75/0.61  % (680)------------------------------
% 1.75/0.61  % (668)Success in time 0.24 s
%------------------------------------------------------------------------------
