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
% DateTime   : Thu Dec  3 13:07:43 EST 2020

% Result     : Theorem 3.10s
% Output     : Refutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 590 expanded)
%              Number of leaves         :   48 ( 242 expanded)
%              Depth                    :   15
%              Number of atoms          :  887 (3957 expanded)
%              Number of equality atoms :  129 ( 851 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f275,f1047,f1434,f1472,f1785,f1918,f2533,f4171,f4333,f4517,f5011,f5042,f5049,f5050,f5079,f5152,f5175,f5326,f5355,f5523])).

fof(f5523,plain,(
    ~ spl17_153 ),
    inference(avatar_contradiction_clause,[],[f5522])).

fof(f5522,plain,
    ( $false
    | ~ spl17_153 ),
    inference(subsumption_resolution,[],[f5521,f223])).

fof(f223,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f156,f124])).

fof(f124,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f5521,plain,
    ( ~ r1_tarski(k1_xboole_0,sK7)
    | ~ spl17_153 ),
    inference(subsumption_resolution,[],[f5513,f118])).

fof(f118,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))
    & k1_xboole_0 != sK7
    & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    & m1_subset_1(sK11,sK7)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    & v1_funct_1(sK10)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK9,sK7,sK8)
    & v1_funct_1(sK9)
    & ~ v1_xboole_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f35,f81,f80,f79,f78])).

fof(f78,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK7
                  & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4))
                  & m1_subset_1(X5,sK7) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
          & v1_funct_2(X3,sK7,sK8)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK7
                & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4))
                & m1_subset_1(X5,sK7) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
        & v1_funct_2(X3,sK7,sK8)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(sK9,X5))
              & k1_xboole_0 != sK7
              & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,X4))
              & m1_subset_1(X5,sK7) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      & v1_funct_2(sK9,sK7,sK8)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(sK9,X5))
            & k1_xboole_0 != sK7
            & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,X4))
            & m1_subset_1(X5,sK7) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X5) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,X5))
          & k1_xboole_0 != sK7
          & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
          & m1_subset_1(X5,sK7) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X5) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,X5))
        & k1_xboole_0 != sK7
        & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
        & m1_subset_1(X5,sK7) )
   => ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))
      & k1_xboole_0 != sK7
      & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
      & m1_subset_1(sK11,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f5513,plain,
    ( k1_xboole_0 = sK7
    | ~ r1_tarski(k1_xboole_0,sK7)
    | ~ spl17_153 ),
    inference(resolution,[],[f5504,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5504,plain,
    ( r1_tarski(sK7,k1_xboole_0)
    | ~ spl17_153 ),
    inference(resolution,[],[f4575,f156])).

fof(f4575,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))
    | ~ spl17_153 ),
    inference(avatar_component_clause,[],[f4574])).

fof(f4574,plain,
    ( spl17_153
  <=> m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_153])])).

fof(f5355,plain,
    ( spl17_7
    | spl17_72 ),
    inference(avatar_split_clause,[],[f5354,f1955,f272])).

fof(f272,plain,
    ( spl17_7
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_7])])).

fof(f1955,plain,
    ( spl17_72
  <=> sP3(sK8,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_72])])).

fof(f5354,plain,
    ( sP3(sK8,sK7,sK9)
    | v1_xboole_0(sK7) ),
    inference(subsumption_resolution,[],[f5353,f112])).

fof(f112,plain,(
    v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f5353,plain,
    ( sP3(sK8,sK7,sK9)
    | v1_xboole_0(sK7)
    | ~ v1_funct_2(sK9,sK7,sK8) ),
    inference(subsumption_resolution,[],[f5352,f110])).

fof(f110,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f82])).

fof(f5352,plain,
    ( sP3(sK8,sK7,sK9)
    | v1_xboole_0(sK8)
    | v1_xboole_0(sK7)
    | ~ v1_funct_2(sK9,sK7,sK8) ),
    inference(subsumption_resolution,[],[f4705,f111])).

fof(f111,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f82])).

fof(f4705,plain,
    ( ~ v1_funct_1(sK9)
    | sP3(sK8,sK7,sK9)
    | v1_xboole_0(sK8)
    | v1_xboole_0(sK7)
    | ~ v1_funct_2(sK9,sK7,sK8) ),
    inference(resolution,[],[f1201,f224])).

fof(f224,plain,(
    r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[],[f156,f113])).

fof(f113,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f82])).

fof(f1201,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X6,k2_zfmisc_1(X7,X8))
      | ~ v1_funct_1(X6)
      | sP3(X8,X7,X6)
      | v1_xboole_0(X8)
      | v1_xboole_0(X7)
      | ~ v1_funct_2(X6,X7,X8) ) ),
    inference(resolution,[],[f150,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP3(X1,X0,X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP3(X1,X0,X2)
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f48,f72])).

fof(f72,plain,(
    ! [X1,X0,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f5326,plain,
    ( ~ spl17_73
    | ~ spl17_72 ),
    inference(avatar_split_clause,[],[f2175,f1955,f1977])).

fof(f1977,plain,
    ( spl17_73
  <=> v1_xboole_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_73])])).

fof(f2175,plain,
    ( ~ v1_xboole_0(sK9)
    | ~ spl17_72 ),
    inference(resolution,[],[f1957,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X1,X0)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ! [X1,X0,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f1957,plain,
    ( sP3(sK8,sK7,sK9)
    | ~ spl17_72 ),
    inference(avatar_component_clause,[],[f1955])).

fof(f5175,plain,
    ( ~ spl17_7
    | spl17_153 ),
    inference(avatar_split_clause,[],[f4593,f4574,f272])).

fof(f4593,plain,
    ( ~ v1_xboole_0(sK7)
    | spl17_153 ),
    inference(resolution,[],[f4576,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f124,f128])).

fof(f128,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f4576,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))
    | spl17_153 ),
    inference(avatar_component_clause,[],[f4574])).

fof(f5152,plain,
    ( ~ spl17_6
    | spl17_26
    | ~ spl17_31
    | ~ spl17_137 ),
    inference(avatar_split_clause,[],[f5148,f4314,f1033,f930,f268])).

fof(f268,plain,
    ( spl17_6
  <=> r2_hidden(sK11,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f930,plain,
    ( spl17_26
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_26])])).

fof(f1033,plain,
    ( spl17_31
  <=> r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_31])])).

fof(f4314,plain,
    ( spl17_137
  <=> ! [X0] :
        ( ~ r2_hidden(sK11,X0)
        | ~ sP5(k1_relat_1(sK10),X0,sK9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_137])])).

fof(f5148,plain,
    ( ~ r2_hidden(sK11,sK7)
    | spl17_26
    | ~ spl17_31
    | ~ spl17_137 ),
    inference(resolution,[],[f4315,f5078])).

fof(f5078,plain,
    ( sP5(k1_relat_1(sK10),sK7,sK9)
    | spl17_26
    | ~ spl17_31 ),
    inference(subsumption_resolution,[],[f5077,f224])).

fof(f5077,plain,
    ( sP5(k1_relat_1(sK10),sK7,sK9)
    | ~ r1_tarski(sK9,k2_zfmisc_1(sK7,sK8))
    | spl17_26
    | ~ spl17_31 ),
    inference(subsumption_resolution,[],[f5076,f111])).

fof(f5076,plain,
    ( sP5(k1_relat_1(sK10),sK7,sK9)
    | ~ v1_funct_1(sK9)
    | ~ r1_tarski(sK9,k2_zfmisc_1(sK7,sK8))
    | spl17_26
    | ~ spl17_31 ),
    inference(subsumption_resolution,[],[f5075,f112])).

fof(f5075,plain,
    ( sP5(k1_relat_1(sK10),sK7,sK9)
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | ~ r1_tarski(sK9,k2_zfmisc_1(sK7,sK8))
    | spl17_26
    | ~ spl17_31 ),
    inference(subsumption_resolution,[],[f5066,f931])).

fof(f931,plain,
    ( k1_xboole_0 != sK8
    | spl17_26 ),
    inference(avatar_component_clause,[],[f930])).

fof(f5066,plain,
    ( k1_xboole_0 = sK8
    | sP5(k1_relat_1(sK10),sK7,sK9)
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | ~ r1_tarski(sK9,k2_zfmisc_1(sK7,sK8))
    | ~ spl17_31 ),
    inference(resolution,[],[f1035,f1553])).

fof(f1553,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tarski(k2_relset_1(X9,X8,X10),X11)
      | k1_xboole_0 = X8
      | sP5(X11,X9,X10)
      | ~ v1_funct_2(X10,X9,X8)
      | ~ v1_funct_1(X10)
      | ~ r1_tarski(X10,k2_zfmisc_1(X9,X8)) ) ),
    inference(resolution,[],[f178,f157])).

fof(f178,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | sP5(X2,X0,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( sP5(X2,X0,X3)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_folding,[],[f67,f76])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ~ sP5(X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f1035,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relat_1(sK10))
    | ~ spl17_31 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f4315,plain,
    ( ! [X0] :
        ( ~ sP5(k1_relat_1(sK10),X0,sK9)
        | ~ r2_hidden(sK11,X0) )
    | ~ spl17_137 ),
    inference(avatar_component_clause,[],[f4314])).

fof(f5079,plain,
    ( ~ spl17_33
    | spl17_47
    | ~ spl17_31 ),
    inference(avatar_split_clause,[],[f5072,f1033,f1377,f1043])).

fof(f1043,plain,
    ( spl17_33
  <=> r1_tarski(k1_relat_1(sK10),k2_relset_1(sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_33])])).

fof(f1377,plain,
    ( spl17_47
  <=> k2_relset_1(sK7,sK8,sK9) = k1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_47])])).

fof(f5072,plain,
    ( k2_relset_1(sK7,sK8,sK9) = k1_relat_1(sK10)
    | ~ r1_tarski(k1_relat_1(sK10),k2_relset_1(sK7,sK8,sK9))
    | ~ spl17_31 ),
    inference(resolution,[],[f1035,f155])).

fof(f5050,plain,
    ( ~ spl17_32
    | spl17_33 ),
    inference(avatar_split_clause,[],[f1619,f1043,f1038])).

fof(f1038,plain,
    ( spl17_32
  <=> v1_xboole_0(k1_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_32])])).

fof(f1619,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK10))
    | spl17_33 ),
    inference(resolution,[],[f1045,f227])).

fof(f227,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f223,f128])).

fof(f1045,plain,
    ( ~ r1_tarski(k1_relat_1(sK10),k2_relset_1(sK7,sK8,sK9))
    | spl17_33 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f5049,plain,
    ( spl17_137
    | spl17_65
    | spl17_136 ),
    inference(avatar_split_clause,[],[f4363,f4310,f1781,f4314])).

fof(f1781,plain,
    ( spl17_65
  <=> k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_65])])).

fof(f4310,plain,
    ( spl17_136
  <=> k1_xboole_0 = k1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_136])])).

fof(f4363,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK11,X0)
        | ~ sP5(k1_relat_1(sK10),X0,sK9) )
    | spl17_65
    | spl17_136 ),
    inference(subsumption_resolution,[],[f4361,f4311])).

fof(f4311,plain,
    ( k1_xboole_0 != k1_relat_1(sK10)
    | spl17_136 ),
    inference(avatar_component_clause,[],[f4310])).

fof(f4361,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK11,X0)
        | k1_xboole_0 = k1_relat_1(sK10)
        | ~ sP5(k1_relat_1(sK10),X0,sK9) )
    | spl17_65 ),
    inference(resolution,[],[f2461,f1397])).

fof(f1397,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ sP5(X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f1396,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | v1_funct_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ~ sP5(X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f76])).

fof(f1396,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ v1_funct_2(X3,X2,X0)
      | ~ sP5(X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f1382,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f1382,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ v1_funct_2(X3,X2,X0)
      | ~ v1_funct_1(X3)
      | ~ sP5(X0,X2,X3) ) ),
    inference(resolution,[],[f174,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f2461,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | spl17_65 ),
    inference(subsumption_resolution,[],[f2460,f306])).

fof(f306,plain,(
    v1_relat_1(sK10) ),
    inference(resolution,[],[f163,f115])).

fof(f115,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f82])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2460,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | ~ v1_relat_1(sK10)
    | spl17_65 ),
    inference(subsumption_resolution,[],[f2459,f536])).

fof(f536,plain,(
    v5_relat_1(sK10,sK6) ),
    inference(resolution,[],[f166,f115])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2459,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | ~ v5_relat_1(sK10,sK6)
    | ~ v1_relat_1(sK10)
    | spl17_65 ),
    inference(subsumption_resolution,[],[f2458,f114])).

fof(f114,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f82])).

fof(f2458,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v5_relat_1(sK10,sK6)
    | ~ v1_relat_1(sK10)
    | spl17_65 ),
    inference(trivial_inequality_removal,[],[f2457])).

fof(f2457,plain,
    ( k1_funct_1(sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v5_relat_1(sK10,sK6)
    | ~ v1_relat_1(sK10)
    | spl17_65 ),
    inference(superposition,[],[f1783,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f1783,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | spl17_65 ),
    inference(avatar_component_clause,[],[f1781])).

fof(f5042,plain,(
    spl17_135 ),
    inference(avatar_split_clause,[],[f117,f4168])).

fof(f4168,plain,
    ( spl17_135
  <=> r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_135])])).

fof(f117,plain,(
    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(cnf_transformation,[],[f82])).

fof(f5011,plain,
    ( ~ spl17_32
    | ~ spl17_52 ),
    inference(avatar_split_clause,[],[f4523,f1656,f1038])).

fof(f1656,plain,
    ( spl17_52
  <=> r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_52])])).

fof(f4523,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK10))
    | ~ spl17_52 ),
    inference(resolution,[],[f1658,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f195,f128])).

fof(f195,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f141,f184])).

fof(f184,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f141,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f1658,plain,
    ( r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10))
    | ~ spl17_52 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f4517,plain,
    ( spl17_52
    | spl17_7
    | ~ spl17_47
    | spl17_51
    | ~ spl17_64 ),
    inference(avatar_split_clause,[],[f4516,f1776,f1652,f1377,f272,f1656])).

fof(f1652,plain,
    ( spl17_51
  <=> k1_xboole_0 = k1_relset_1(sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_51])])).

fof(f1776,plain,
    ( spl17_64
  <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_64])])).

fof(f4516,plain,
    ( r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10))
    | spl17_7
    | ~ spl17_47
    | spl17_51
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f4515,f273])).

fof(f273,plain,
    ( ~ v1_xboole_0(sK7)
    | spl17_7 ),
    inference(avatar_component_clause,[],[f272])).

fof(f4515,plain,
    ( r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10))
    | v1_xboole_0(sK7)
    | ~ spl17_47
    | spl17_51
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f4514,f110])).

fof(f4514,plain,
    ( r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10))
    | v1_xboole_0(sK8)
    | v1_xboole_0(sK7)
    | ~ spl17_47
    | spl17_51
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f4513,f1777])).

fof(f1777,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ spl17_64 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f4513,plain,
    ( r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | v1_xboole_0(sK8)
    | v1_xboole_0(sK7)
    | ~ spl17_47
    | spl17_51 ),
    inference(subsumption_resolution,[],[f4508,f1653])).

fof(f1653,plain,
    ( k1_xboole_0 != k1_relset_1(sK7,sK8,sK9)
    | spl17_51 ),
    inference(avatar_component_clause,[],[f1652])).

fof(f4508,plain,
    ( r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10))
    | k1_xboole_0 = k1_relset_1(sK7,sK8,sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | v1_xboole_0(sK8)
    | v1_xboole_0(sK7)
    | ~ spl17_47 ),
    inference(superposition,[],[f126,f1379])).

fof(f1379,plain,
    ( k2_relset_1(sK7,sK8,sK9) = k1_relat_1(sK10)
    | ~ spl17_47 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),k2_relset_1(X0,X1,X2))
      | k1_xboole_0 = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(sK12(X0,X1,X2),k2_relset_1(X0,X1,X2))
                & m1_subset_1(sK12(X0,X1,X2),X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f37,f83])).

fof(f83,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
          & m1_subset_1(X3,X1) )
     => ( r2_hidden(sK12(X0,X1,X2),k2_relset_1(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  & m1_subset_1(X3,X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  & m1_subset_1(X3,X1) )
              | k1_xboole_0 = k1_relset_1(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f4333,plain,
    ( spl17_32
    | ~ spl17_136 ),
    inference(avatar_contradiction_clause,[],[f4332])).

fof(f4332,plain,
    ( $false
    | spl17_32
    | ~ spl17_136 ),
    inference(subsumption_resolution,[],[f4317,f120])).

fof(f120,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f4317,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl17_32
    | ~ spl17_136 ),
    inference(backward_demodulation,[],[f1040,f4312])).

fof(f4312,plain,
    ( k1_xboole_0 = k1_relat_1(sK10)
    | ~ spl17_136 ),
    inference(avatar_component_clause,[],[f4310])).

fof(f1040,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK10))
    | spl17_32 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f4171,plain,
    ( ~ spl17_30
    | ~ spl17_135
    | ~ spl17_65
    | ~ spl17_64 ),
    inference(avatar_split_clause,[],[f4166,f1776,f1781,f4168,f1029])).

fof(f1029,plain,
    ( spl17_30
  <=> m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_30])])).

fof(f4166,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f4165,f110])).

fof(f4165,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | v1_xboole_0(sK8)
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f4164,f111])).

fof(f4164,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8)
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f4163,f112])).

fof(f4163,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8)
    | ~ spl17_64 ),
    inference(subsumption_resolution,[],[f4162,f1777])).

fof(f4162,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f4161,f114])).

fof(f4161,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f4160,f116])).

fof(f116,plain,(
    m1_subset_1(sK11,sK7) ),
    inference(cnf_transformation,[],[f82])).

fof(f4160,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK11,sK7)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f4159,f118])).

fof(f4159,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | k1_xboole_0 = sK7
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK11,sK7)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(superposition,[],[f119,f162])).

fof(f162,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f119,plain,(
    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f82])).

fof(f2533,plain,
    ( ~ spl17_71
    | spl17_73 ),
    inference(avatar_contradiction_clause,[],[f2532])).

fof(f2532,plain,
    ( $false
    | ~ spl17_71
    | spl17_73 ),
    inference(subsumption_resolution,[],[f2531,f120])).

fof(f2531,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl17_71
    | spl17_73 ),
    inference(subsumption_resolution,[],[f2528,f1978])).

fof(f1978,plain,
    ( ~ v1_xboole_0(sK9)
    | spl17_73 ),
    inference(avatar_component_clause,[],[f1977])).

fof(f2528,plain,
    ( v1_xboole_0(sK9)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl17_71 ),
    inference(resolution,[],[f712,f2498])).

fof(f2498,plain,
    ( ! [X1] : sP4(X1,k1_xboole_0,sK9)
    | ~ spl17_71 ),
    inference(subsumption_resolution,[],[f2497,f305])).

fof(f305,plain,(
    v1_relat_1(sK9) ),
    inference(resolution,[],[f163,f113])).

fof(f2497,plain,
    ( ! [X1] :
        ( sP4(X1,k1_xboole_0,sK9)
        | ~ v1_relat_1(sK9) )
    | ~ spl17_71 ),
    inference(subsumption_resolution,[],[f2496,f111])).

fof(f2496,plain,
    ( ! [X1] :
        ( sP4(X1,k1_xboole_0,sK9)
        | ~ v1_funct_1(sK9)
        | ~ v1_relat_1(sK9) )
    | ~ spl17_71 ),
    inference(subsumption_resolution,[],[f2489,f195])).

fof(f2489,plain,
    ( ! [X1] :
        ( r2_hidden(sK16(k1_xboole_0,X1,sK9),k1_xboole_0)
        | sP4(X1,k1_xboole_0,sK9)
        | ~ v1_funct_1(sK9)
        | ~ v1_relat_1(sK9) )
    | ~ spl17_71 ),
    inference(superposition,[],[f187,f1916])).

fof(f1916,plain,
    ( k1_xboole_0 = k1_relat_1(sK9)
    | ~ spl17_71 ),
    inference(avatar_component_clause,[],[f1914])).

fof(f1914,plain,
    ( spl17_71
  <=> k1_xboole_0 = k1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_71])])).

fof(f187,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK16(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP4(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X0,X2)
      | r2_hidden(sK16(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( sP4(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK16(X0,X1,X2)),X1)
        & r2_hidden(sK16(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f75,f106])).

fof(f106,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK16(X0,X1,X2)),X1)
        & r2_hidden(sK16(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( sP4(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f60,f74])).

fof(f74,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP4(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f712,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f169,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f104])).

fof(f104,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP4(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f74])).

fof(f1918,plain,
    ( ~ spl17_64
    | spl17_71
    | ~ spl17_51 ),
    inference(avatar_split_clause,[],[f1912,f1652,f1914,f1776])).

fof(f1912,plain,
    ( k1_xboole_0 = k1_relat_1(sK9)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ spl17_51 ),
    inference(superposition,[],[f164,f1654])).

fof(f1654,plain,
    ( k1_xboole_0 = k1_relset_1(sK7,sK8,sK9)
    | ~ spl17_51 ),
    inference(avatar_component_clause,[],[f1652])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1785,plain,(
    spl17_64 ),
    inference(avatar_split_clause,[],[f113,f1776])).

fof(f1472,plain,
    ( ~ spl17_30
    | spl17_31 ),
    inference(avatar_split_clause,[],[f1469,f1033,f1029])).

fof(f1469,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relat_1(sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(superposition,[],[f117,f164])).

fof(f1434,plain,(
    ~ spl17_26 ),
    inference(avatar_contradiction_clause,[],[f1433])).

fof(f1433,plain,
    ( $false
    | ~ spl17_26 ),
    inference(subsumption_resolution,[],[f1407,f120])).

fof(f1407,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl17_26 ),
    inference(backward_demodulation,[],[f110,f932])).

fof(f932,plain,
    ( k1_xboole_0 = sK8
    | ~ spl17_26 ),
    inference(avatar_component_clause,[],[f930])).

fof(f1047,plain,(
    spl17_30 ),
    inference(avatar_split_clause,[],[f115,f1029])).

fof(f275,plain,
    ( spl17_6
    | spl17_7 ),
    inference(avatar_split_clause,[],[f260,f272,f268])).

fof(f260,plain,
    ( v1_xboole_0(sK7)
    | r2_hidden(sK11,sK7) ),
    inference(resolution,[],[f146,f116])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:03:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (12310)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.49  % (12302)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (12293)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.13/0.51  % (12298)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.13/0.51  % (12295)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.13/0.51  % (12300)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.13/0.52  % (12301)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.13/0.52  % (12307)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.13/0.52  % (12299)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.13/0.52  % (12294)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.13/0.52  % (12308)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.13/0.52  % (12312)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.13/0.53  % (12306)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.13/0.53  % (12316)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.13/0.53  % (12297)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.13/0.53  % (12303)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.13/0.53  % (12311)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.13/0.53  % (12315)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.13/0.53  % (12314)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.13/0.53  % (12304)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.33/0.54  % (12317)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.33/0.54  % (12309)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.33/0.55  % (12305)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.33/0.55  % (12296)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.33/0.55  % (12313)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.33/0.55  % (12318)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 3.10/0.81  % (12297)Refutation found. Thanks to Tanya!
% 3.10/0.81  % SZS status Theorem for theBenchmark
% 3.10/0.82  % SZS output start Proof for theBenchmark
% 3.10/0.82  fof(f5524,plain,(
% 3.10/0.82    $false),
% 3.10/0.82    inference(avatar_sat_refutation,[],[f275,f1047,f1434,f1472,f1785,f1918,f2533,f4171,f4333,f4517,f5011,f5042,f5049,f5050,f5079,f5152,f5175,f5326,f5355,f5523])).
% 3.10/0.82  fof(f5523,plain,(
% 3.10/0.82    ~spl17_153),
% 3.10/0.82    inference(avatar_contradiction_clause,[],[f5522])).
% 3.10/0.82  fof(f5522,plain,(
% 3.10/0.82    $false | ~spl17_153),
% 3.10/0.82    inference(subsumption_resolution,[],[f5521,f223])).
% 3.10/0.82  fof(f223,plain,(
% 3.10/0.82    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 3.10/0.82    inference(resolution,[],[f156,f124])).
% 3.10/0.82  fof(f124,plain,(
% 3.10/0.82    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.10/0.82    inference(cnf_transformation,[],[f8])).
% 3.10/0.82  fof(f8,axiom,(
% 3.10/0.82    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.10/0.82  fof(f156,plain,(
% 3.10/0.82    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f101])).
% 3.10/0.82  fof(f101,plain,(
% 3.10/0.82    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.10/0.82    inference(nnf_transformation,[],[f11])).
% 3.10/0.82  fof(f11,axiom,(
% 3.10/0.82    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.10/0.82  fof(f5521,plain,(
% 3.10/0.82    ~r1_tarski(k1_xboole_0,sK7) | ~spl17_153),
% 3.10/0.82    inference(subsumption_resolution,[],[f5513,f118])).
% 3.10/0.82  fof(f118,plain,(
% 3.10/0.82    k1_xboole_0 != sK7),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f82,plain,(
% 3.10/0.82    (((k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(sK11,sK7)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(sK10)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9)) & ~v1_xboole_0(sK8)),
% 3.10/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f35,f81,f80,f79,f78])).
% 3.10/0.82  fof(f78,plain,(
% 3.10/0.82    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(X3,sK7,sK8) & v1_funct_1(X3)) & ~v1_xboole_0(sK8))),
% 3.10/0.82    introduced(choice_axiom,[])).
% 3.10/0.82  fof(f79,plain,(
% 3.10/0.82    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(X3,sK7,sK8) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(sK9,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9))),
% 3.10/0.82    introduced(choice_axiom,[])).
% 3.10/0.82  fof(f80,plain,(
% 3.10/0.82    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(sK9,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X5) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(X5,sK7)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(sK10))),
% 3.10/0.82    introduced(choice_axiom,[])).
% 3.10/0.82  fof(f81,plain,(
% 3.10/0.82    ? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X5) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(X5,sK7)) => (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(sK11,sK7))),
% 3.10/0.82    introduced(choice_axiom,[])).
% 3.10/0.82  fof(f35,plain,(
% 3.10/0.82    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.10/0.82    inference(flattening,[],[f34])).
% 3.10/0.82  fof(f34,plain,(
% 3.10/0.82    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.10/0.82    inference(ennf_transformation,[],[f33])).
% 3.10/0.82  fof(f33,negated_conjecture,(
% 3.10/0.82    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.10/0.82    inference(negated_conjecture,[],[f32])).
% 3.10/0.82  fof(f32,conjecture,(
% 3.10/0.82    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 3.10/0.82  fof(f5513,plain,(
% 3.10/0.82    k1_xboole_0 = sK7 | ~r1_tarski(k1_xboole_0,sK7) | ~spl17_153),
% 3.10/0.82    inference(resolution,[],[f5504,f155])).
% 3.10/0.82  fof(f155,plain,(
% 3.10/0.82    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f100])).
% 3.10/0.82  fof(f100,plain,(
% 3.10/0.82    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/0.82    inference(flattening,[],[f99])).
% 3.10/0.82  fof(f99,plain,(
% 3.10/0.82    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/0.82    inference(nnf_transformation,[],[f3])).
% 3.10/0.82  fof(f3,axiom,(
% 3.10/0.82    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.10/0.82  fof(f5504,plain,(
% 3.10/0.82    r1_tarski(sK7,k1_xboole_0) | ~spl17_153),
% 3.10/0.82    inference(resolution,[],[f4575,f156])).
% 3.10/0.82  fof(f4575,plain,(
% 3.10/0.82    m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) | ~spl17_153),
% 3.10/0.82    inference(avatar_component_clause,[],[f4574])).
% 3.10/0.82  fof(f4574,plain,(
% 3.10/0.82    spl17_153 <=> m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_153])])).
% 3.10/0.82  fof(f5355,plain,(
% 3.10/0.82    spl17_7 | spl17_72),
% 3.10/0.82    inference(avatar_split_clause,[],[f5354,f1955,f272])).
% 3.10/0.82  fof(f272,plain,(
% 3.10/0.82    spl17_7 <=> v1_xboole_0(sK7)),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_7])])).
% 3.10/0.82  fof(f1955,plain,(
% 3.10/0.82    spl17_72 <=> sP3(sK8,sK7,sK9)),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_72])])).
% 3.10/0.82  fof(f5354,plain,(
% 3.10/0.82    sP3(sK8,sK7,sK9) | v1_xboole_0(sK7)),
% 3.10/0.82    inference(subsumption_resolution,[],[f5353,f112])).
% 3.10/0.82  fof(f112,plain,(
% 3.10/0.82    v1_funct_2(sK9,sK7,sK8)),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f5353,plain,(
% 3.10/0.82    sP3(sK8,sK7,sK9) | v1_xboole_0(sK7) | ~v1_funct_2(sK9,sK7,sK8)),
% 3.10/0.82    inference(subsumption_resolution,[],[f5352,f110])).
% 3.10/0.82  fof(f110,plain,(
% 3.10/0.82    ~v1_xboole_0(sK8)),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f5352,plain,(
% 3.10/0.82    sP3(sK8,sK7,sK9) | v1_xboole_0(sK8) | v1_xboole_0(sK7) | ~v1_funct_2(sK9,sK7,sK8)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4705,f111])).
% 3.10/0.82  fof(f111,plain,(
% 3.10/0.82    v1_funct_1(sK9)),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f4705,plain,(
% 3.10/0.82    ~v1_funct_1(sK9) | sP3(sK8,sK7,sK9) | v1_xboole_0(sK8) | v1_xboole_0(sK7) | ~v1_funct_2(sK9,sK7,sK8)),
% 3.10/0.82    inference(resolution,[],[f1201,f224])).
% 3.10/0.82  fof(f224,plain,(
% 3.10/0.82    r1_tarski(sK9,k2_zfmisc_1(sK7,sK8))),
% 3.10/0.82    inference(resolution,[],[f156,f113])).
% 3.10/0.82  fof(f113,plain,(
% 3.10/0.82    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f1201,plain,(
% 3.10/0.82    ( ! [X6,X8,X7] : (~r1_tarski(X6,k2_zfmisc_1(X7,X8)) | ~v1_funct_1(X6) | sP3(X8,X7,X6) | v1_xboole_0(X8) | v1_xboole_0(X7) | ~v1_funct_2(X6,X7,X8)) )),
% 3.10/0.82    inference(resolution,[],[f150,f157])).
% 3.10/0.82  fof(f157,plain,(
% 3.10/0.82    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f101])).
% 3.10/0.82  fof(f150,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | sP3(X1,X0,X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f73])).
% 3.10/0.82  fof(f73,plain,(
% 3.10/0.82    ! [X0,X1] : (! [X2] : (sP3(X1,X0,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.10/0.82    inference(definition_folding,[],[f48,f72])).
% 3.10/0.82  fof(f72,plain,(
% 3.10/0.82    ! [X1,X0,X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 3.10/0.82    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 3.10/0.82  fof(f48,plain,(
% 3.10/0.82    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.10/0.82    inference(flattening,[],[f47])).
% 3.10/0.82  fof(f47,plain,(
% 3.10/0.82    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.10/0.82    inference(ennf_transformation,[],[f26])).
% 3.10/0.82  fof(f26,axiom,(
% 3.10/0.82    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 3.10/0.82  fof(f5326,plain,(
% 3.10/0.82    ~spl17_73 | ~spl17_72),
% 3.10/0.82    inference(avatar_split_clause,[],[f2175,f1955,f1977])).
% 3.10/0.82  fof(f1977,plain,(
% 3.10/0.82    spl17_73 <=> v1_xboole_0(sK9)),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_73])])).
% 3.10/0.82  fof(f2175,plain,(
% 3.10/0.82    ~v1_xboole_0(sK9) | ~spl17_72),
% 3.10/0.82    inference(resolution,[],[f1957,f148])).
% 3.10/0.82  fof(f148,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~v1_xboole_0(X2)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f98])).
% 3.10/0.82  fof(f98,plain,(
% 3.10/0.82    ! [X0,X1,X2] : ((v1_funct_2(X2,X1,X0) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP3(X0,X1,X2))),
% 3.10/0.82    inference(rectify,[],[f97])).
% 3.10/0.82  fof(f97,plain,(
% 3.10/0.82    ! [X1,X0,X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 3.10/0.82    inference(nnf_transformation,[],[f72])).
% 3.10/0.82  fof(f1957,plain,(
% 3.10/0.82    sP3(sK8,sK7,sK9) | ~spl17_72),
% 3.10/0.82    inference(avatar_component_clause,[],[f1955])).
% 3.10/0.82  fof(f5175,plain,(
% 3.10/0.82    ~spl17_7 | spl17_153),
% 3.10/0.82    inference(avatar_split_clause,[],[f4593,f4574,f272])).
% 3.10/0.82  fof(f4593,plain,(
% 3.10/0.82    ~v1_xboole_0(sK7) | spl17_153),
% 3.10/0.82    inference(resolution,[],[f4576,f190])).
% 3.10/0.82  fof(f190,plain,(
% 3.10/0.82    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 3.10/0.82    inference(superposition,[],[f124,f128])).
% 3.10/0.82  fof(f128,plain,(
% 3.10/0.82    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f39])).
% 3.10/0.82  fof(f39,plain,(
% 3.10/0.82    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.10/0.82    inference(ennf_transformation,[],[f2])).
% 3.10/0.82  fof(f2,axiom,(
% 3.10/0.82    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 3.10/0.82  fof(f4576,plain,(
% 3.10/0.82    ~m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) | spl17_153),
% 3.10/0.82    inference(avatar_component_clause,[],[f4574])).
% 3.10/0.82  fof(f5152,plain,(
% 3.10/0.82    ~spl17_6 | spl17_26 | ~spl17_31 | ~spl17_137),
% 3.10/0.82    inference(avatar_split_clause,[],[f5148,f4314,f1033,f930,f268])).
% 3.10/0.82  fof(f268,plain,(
% 3.10/0.82    spl17_6 <=> r2_hidden(sK11,sK7)),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).
% 3.10/0.82  fof(f930,plain,(
% 3.10/0.82    spl17_26 <=> k1_xboole_0 = sK8),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_26])])).
% 3.10/0.82  fof(f1033,plain,(
% 3.10/0.82    spl17_31 <=> r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relat_1(sK10))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_31])])).
% 3.10/0.82  fof(f4314,plain,(
% 3.10/0.82    spl17_137 <=> ! [X0] : (~r2_hidden(sK11,X0) | ~sP5(k1_relat_1(sK10),X0,sK9))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_137])])).
% 3.10/0.82  fof(f5148,plain,(
% 3.10/0.82    ~r2_hidden(sK11,sK7) | (spl17_26 | ~spl17_31 | ~spl17_137)),
% 3.10/0.82    inference(resolution,[],[f4315,f5078])).
% 3.10/0.82  fof(f5078,plain,(
% 3.10/0.82    sP5(k1_relat_1(sK10),sK7,sK9) | (spl17_26 | ~spl17_31)),
% 3.10/0.82    inference(subsumption_resolution,[],[f5077,f224])).
% 3.10/0.82  fof(f5077,plain,(
% 3.10/0.82    sP5(k1_relat_1(sK10),sK7,sK9) | ~r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) | (spl17_26 | ~spl17_31)),
% 3.10/0.82    inference(subsumption_resolution,[],[f5076,f111])).
% 3.10/0.82  fof(f5076,plain,(
% 3.10/0.82    sP5(k1_relat_1(sK10),sK7,sK9) | ~v1_funct_1(sK9) | ~r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) | (spl17_26 | ~spl17_31)),
% 3.10/0.82    inference(subsumption_resolution,[],[f5075,f112])).
% 3.10/0.82  fof(f5075,plain,(
% 3.10/0.82    sP5(k1_relat_1(sK10),sK7,sK9) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | ~r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) | (spl17_26 | ~spl17_31)),
% 3.10/0.82    inference(subsumption_resolution,[],[f5066,f931])).
% 3.10/0.82  fof(f931,plain,(
% 3.10/0.82    k1_xboole_0 != sK8 | spl17_26),
% 3.10/0.82    inference(avatar_component_clause,[],[f930])).
% 3.10/0.82  fof(f5066,plain,(
% 3.10/0.82    k1_xboole_0 = sK8 | sP5(k1_relat_1(sK10),sK7,sK9) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | ~r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) | ~spl17_31),
% 3.10/0.82    inference(resolution,[],[f1035,f1553])).
% 3.10/0.82  fof(f1553,plain,(
% 3.10/0.82    ( ! [X10,X8,X11,X9] : (~r1_tarski(k2_relset_1(X9,X8,X10),X11) | k1_xboole_0 = X8 | sP5(X11,X9,X10) | ~v1_funct_2(X10,X9,X8) | ~v1_funct_1(X10) | ~r1_tarski(X10,k2_zfmisc_1(X9,X8))) )),
% 3.10/0.82    inference(resolution,[],[f178,f157])).
% 3.10/0.82  fof(f178,plain,(
% 3.10/0.82    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | sP5(X2,X0,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f77])).
% 3.10/0.82  fof(f77,plain,(
% 3.10/0.82    ! [X0,X1,X2,X3] : (sP5(X2,X0,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.10/0.82    inference(definition_folding,[],[f67,f76])).
% 3.10/0.82  fof(f76,plain,(
% 3.10/0.82    ! [X2,X0,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | ~sP5(X2,X0,X3))),
% 3.10/0.82    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 3.10/0.82  fof(f67,plain,(
% 3.10/0.82    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.10/0.82    inference(flattening,[],[f66])).
% 3.10/0.82  fof(f66,plain,(
% 3.10/0.82    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.10/0.82    inference(ennf_transformation,[],[f31])).
% 3.10/0.82  fof(f31,axiom,(
% 3.10/0.82    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 3.10/0.82  fof(f1035,plain,(
% 3.10/0.82    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relat_1(sK10)) | ~spl17_31),
% 3.10/0.82    inference(avatar_component_clause,[],[f1033])).
% 3.10/0.82  fof(f4315,plain,(
% 3.10/0.82    ( ! [X0] : (~sP5(k1_relat_1(sK10),X0,sK9) | ~r2_hidden(sK11,X0)) ) | ~spl17_137),
% 3.10/0.82    inference(avatar_component_clause,[],[f4314])).
% 3.10/0.82  fof(f5079,plain,(
% 3.10/0.82    ~spl17_33 | spl17_47 | ~spl17_31),
% 3.10/0.82    inference(avatar_split_clause,[],[f5072,f1033,f1377,f1043])).
% 3.10/0.82  fof(f1043,plain,(
% 3.10/0.82    spl17_33 <=> r1_tarski(k1_relat_1(sK10),k2_relset_1(sK7,sK8,sK9))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_33])])).
% 3.10/0.82  fof(f1377,plain,(
% 3.10/0.82    spl17_47 <=> k2_relset_1(sK7,sK8,sK9) = k1_relat_1(sK10)),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_47])])).
% 3.10/0.82  fof(f5072,plain,(
% 3.10/0.82    k2_relset_1(sK7,sK8,sK9) = k1_relat_1(sK10) | ~r1_tarski(k1_relat_1(sK10),k2_relset_1(sK7,sK8,sK9)) | ~spl17_31),
% 3.10/0.82    inference(resolution,[],[f1035,f155])).
% 3.10/0.82  fof(f5050,plain,(
% 3.10/0.82    ~spl17_32 | spl17_33),
% 3.10/0.82    inference(avatar_split_clause,[],[f1619,f1043,f1038])).
% 3.10/0.82  fof(f1038,plain,(
% 3.10/0.82    spl17_32 <=> v1_xboole_0(k1_relat_1(sK10))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_32])])).
% 3.10/0.82  fof(f1619,plain,(
% 3.10/0.82    ~v1_xboole_0(k1_relat_1(sK10)) | spl17_33),
% 3.10/0.82    inference(resolution,[],[f1045,f227])).
% 3.10/0.82  fof(f227,plain,(
% 3.10/0.82    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 3.10/0.82    inference(superposition,[],[f223,f128])).
% 3.10/0.82  fof(f1045,plain,(
% 3.10/0.82    ~r1_tarski(k1_relat_1(sK10),k2_relset_1(sK7,sK8,sK9)) | spl17_33),
% 3.10/0.82    inference(avatar_component_clause,[],[f1043])).
% 3.10/0.82  fof(f5049,plain,(
% 3.10/0.82    spl17_137 | spl17_65 | spl17_136),
% 3.10/0.82    inference(avatar_split_clause,[],[f4363,f4310,f1781,f4314])).
% 3.10/0.82  fof(f1781,plain,(
% 3.10/0.82    spl17_65 <=> k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_65])])).
% 3.10/0.82  fof(f4310,plain,(
% 3.10/0.82    spl17_136 <=> k1_xboole_0 = k1_relat_1(sK10)),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_136])])).
% 3.10/0.82  fof(f4363,plain,(
% 3.10/0.82    ( ! [X0] : (~r2_hidden(sK11,X0) | ~sP5(k1_relat_1(sK10),X0,sK9)) ) | (spl17_65 | spl17_136)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4361,f4311])).
% 3.10/0.82  fof(f4311,plain,(
% 3.10/0.82    k1_xboole_0 != k1_relat_1(sK10) | spl17_136),
% 3.10/0.82    inference(avatar_component_clause,[],[f4310])).
% 3.10/0.82  fof(f4361,plain,(
% 3.10/0.82    ( ! [X0] : (~r2_hidden(sK11,X0) | k1_xboole_0 = k1_relat_1(sK10) | ~sP5(k1_relat_1(sK10),X0,sK9)) ) | spl17_65),
% 3.10/0.82    inference(resolution,[],[f2461,f1397])).
% 3.10/0.82  fof(f1397,plain,(
% 3.10/0.82    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X1),X0) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~sP5(X0,X2,X3)) )),
% 3.10/0.82    inference(subsumption_resolution,[],[f1396,f176])).
% 3.10/0.82  fof(f176,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | v1_funct_2(X2,X1,X0)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f109])).
% 3.10/0.82  fof(f109,plain,(
% 3.10/0.82    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP5(X0,X1,X2))),
% 3.10/0.82    inference(rectify,[],[f108])).
% 3.10/0.82  fof(f108,plain,(
% 3.10/0.82    ! [X2,X0,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | ~sP5(X2,X0,X3))),
% 3.10/0.82    inference(nnf_transformation,[],[f76])).
% 3.10/0.82  fof(f1396,plain,(
% 3.10/0.82    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(X3,X1),X0) | ~v1_funct_2(X3,X2,X0) | ~sP5(X0,X2,X3)) )),
% 3.10/0.82    inference(subsumption_resolution,[],[f1382,f175])).
% 3.10/0.82  fof(f175,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | v1_funct_1(X2)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f109])).
% 3.10/0.82  fof(f1382,plain,(
% 3.10/0.82    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(X3,X1),X0) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | ~sP5(X0,X2,X3)) )),
% 3.10/0.82    inference(resolution,[],[f174,f177])).
% 3.10/0.82  fof(f177,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP5(X0,X1,X2)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f109])).
% 3.10/0.82  fof(f174,plain,(
% 3.10/0.82    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f65])).
% 3.10/0.82  fof(f65,plain,(
% 3.10/0.82    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.10/0.82    inference(flattening,[],[f64])).
% 3.10/0.82  fof(f64,plain,(
% 3.10/0.82    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.10/0.82    inference(ennf_transformation,[],[f30])).
% 3.10/0.82  fof(f30,axiom,(
% 3.10/0.82    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 3.10/0.82  fof(f2461,plain,(
% 3.10/0.82    ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | spl17_65),
% 3.10/0.82    inference(subsumption_resolution,[],[f2460,f306])).
% 3.10/0.82  fof(f306,plain,(
% 3.10/0.82    v1_relat_1(sK10)),
% 3.10/0.82    inference(resolution,[],[f163,f115])).
% 3.10/0.82  fof(f115,plain,(
% 3.10/0.82    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f163,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f56])).
% 3.10/0.82  fof(f56,plain,(
% 3.10/0.82    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.82    inference(ennf_transformation,[],[f21])).
% 3.10/0.82  fof(f21,axiom,(
% 3.10/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.10/0.82  fof(f2460,plain,(
% 3.10/0.82    ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | ~v1_relat_1(sK10) | spl17_65),
% 3.10/0.82    inference(subsumption_resolution,[],[f2459,f536])).
% 3.10/0.82  fof(f536,plain,(
% 3.10/0.82    v5_relat_1(sK10,sK6)),
% 3.10/0.82    inference(resolution,[],[f166,f115])).
% 3.10/0.82  fof(f166,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f58])).
% 3.10/0.82  fof(f58,plain,(
% 3.10/0.82    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.82    inference(ennf_transformation,[],[f22])).
% 3.10/0.82  fof(f22,axiom,(
% 3.10/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.10/0.82  fof(f2459,plain,(
% 3.10/0.82    ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | ~v5_relat_1(sK10,sK6) | ~v1_relat_1(sK10) | spl17_65),
% 3.10/0.82    inference(subsumption_resolution,[],[f2458,f114])).
% 3.10/0.82  fof(f114,plain,(
% 3.10/0.82    v1_funct_1(sK10)),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f2458,plain,(
% 3.10/0.82    ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v5_relat_1(sK10,sK6) | ~v1_relat_1(sK10) | spl17_65),
% 3.10/0.82    inference(trivial_inequality_removal,[],[f2457])).
% 3.10/0.82  fof(f2457,plain,(
% 3.10/0.82    k1_funct_1(sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v5_relat_1(sK10,sK6) | ~v1_relat_1(sK10) | spl17_65),
% 3.10/0.82    inference(superposition,[],[f1783,f151])).
% 3.10/0.82  fof(f151,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f50])).
% 3.10/0.82  fof(f50,plain,(
% 3.10/0.82    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.10/0.82    inference(flattening,[],[f49])).
% 3.10/0.82  fof(f49,plain,(
% 3.10/0.82    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.10/0.82    inference(ennf_transformation,[],[f27])).
% 3.10/0.82  fof(f27,axiom,(
% 3.10/0.82    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 3.10/0.82  fof(f1783,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | spl17_65),
% 3.10/0.82    inference(avatar_component_clause,[],[f1781])).
% 3.10/0.82  fof(f5042,plain,(
% 3.10/0.82    spl17_135),
% 3.10/0.82    inference(avatar_split_clause,[],[f117,f4168])).
% 3.10/0.82  fof(f4168,plain,(
% 3.10/0.82    spl17_135 <=> r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_135])])).
% 3.10/0.82  fof(f117,plain,(
% 3.10/0.82    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f5011,plain,(
% 3.10/0.82    ~spl17_32 | ~spl17_52),
% 3.10/0.82    inference(avatar_split_clause,[],[f4523,f1656,f1038])).
% 3.10/0.82  fof(f1656,plain,(
% 3.10/0.82    spl17_52 <=> r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_52])])).
% 3.10/0.82  fof(f4523,plain,(
% 3.10/0.82    ~v1_xboole_0(k1_relat_1(sK10)) | ~spl17_52),
% 3.10/0.82    inference(resolution,[],[f1658,f201])).
% 3.10/0.82  fof(f201,plain,(
% 3.10/0.82    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.10/0.82    inference(superposition,[],[f195,f128])).
% 3.10/0.82  fof(f195,plain,(
% 3.10/0.82    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.10/0.82    inference(superposition,[],[f141,f184])).
% 3.10/0.82  fof(f184,plain,(
% 3.10/0.82    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.10/0.82    inference(equality_resolution,[],[f160])).
% 3.10/0.82  fof(f160,plain,(
% 3.10/0.82    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.10/0.82    inference(cnf_transformation,[],[f103])).
% 3.10/0.82  fof(f103,plain,(
% 3.10/0.82    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/0.82    inference(flattening,[],[f102])).
% 3.10/0.82  fof(f102,plain,(
% 3.10/0.82    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/0.82    inference(nnf_transformation,[],[f4])).
% 3.10/0.82  fof(f4,axiom,(
% 3.10/0.82    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.10/0.82  fof(f141,plain,(
% 3.10/0.82    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.10/0.82    inference(cnf_transformation,[],[f5])).
% 3.10/0.82  fof(f5,axiom,(
% 3.10/0.82    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 3.10/0.82  fof(f1658,plain,(
% 3.10/0.82    r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10)) | ~spl17_52),
% 3.10/0.82    inference(avatar_component_clause,[],[f1656])).
% 3.10/0.82  fof(f4517,plain,(
% 3.10/0.82    spl17_52 | spl17_7 | ~spl17_47 | spl17_51 | ~spl17_64),
% 3.10/0.82    inference(avatar_split_clause,[],[f4516,f1776,f1652,f1377,f272,f1656])).
% 3.10/0.82  fof(f1652,plain,(
% 3.10/0.82    spl17_51 <=> k1_xboole_0 = k1_relset_1(sK7,sK8,sK9)),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_51])])).
% 3.10/0.82  fof(f1776,plain,(
% 3.10/0.82    spl17_64 <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_64])])).
% 3.10/0.82  fof(f4516,plain,(
% 3.10/0.82    r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10)) | (spl17_7 | ~spl17_47 | spl17_51 | ~spl17_64)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4515,f273])).
% 3.10/0.82  fof(f273,plain,(
% 3.10/0.82    ~v1_xboole_0(sK7) | spl17_7),
% 3.10/0.82    inference(avatar_component_clause,[],[f272])).
% 3.10/0.82  fof(f4515,plain,(
% 3.10/0.82    r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10)) | v1_xboole_0(sK7) | (~spl17_47 | spl17_51 | ~spl17_64)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4514,f110])).
% 3.10/0.82  fof(f4514,plain,(
% 3.10/0.82    r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10)) | v1_xboole_0(sK8) | v1_xboole_0(sK7) | (~spl17_47 | spl17_51 | ~spl17_64)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4513,f1777])).
% 3.10/0.82  fof(f1777,plain,(
% 3.10/0.82    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~spl17_64),
% 3.10/0.82    inference(avatar_component_clause,[],[f1776])).
% 3.10/0.82  fof(f4513,plain,(
% 3.10/0.82    r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10)) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | v1_xboole_0(sK8) | v1_xboole_0(sK7) | (~spl17_47 | spl17_51)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4508,f1653])).
% 3.10/0.82  fof(f1653,plain,(
% 3.10/0.82    k1_xboole_0 != k1_relset_1(sK7,sK8,sK9) | spl17_51),
% 3.10/0.82    inference(avatar_component_clause,[],[f1652])).
% 3.10/0.82  fof(f4508,plain,(
% 3.10/0.82    r2_hidden(sK12(sK7,sK8,sK9),k1_relat_1(sK10)) | k1_xboole_0 = k1_relset_1(sK7,sK8,sK9) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | v1_xboole_0(sK8) | v1_xboole_0(sK7) | ~spl17_47),
% 3.10/0.82    inference(superposition,[],[f126,f1379])).
% 3.10/0.82  fof(f1379,plain,(
% 3.10/0.82    k2_relset_1(sK7,sK8,sK9) = k1_relat_1(sK10) | ~spl17_47),
% 3.10/0.82    inference(avatar_component_clause,[],[f1377])).
% 3.10/0.82  fof(f126,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (r2_hidden(sK12(X0,X1,X2),k2_relset_1(X0,X1,X2)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f84])).
% 3.10/0.82  fof(f84,plain,(
% 3.10/0.82    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(sK12(X0,X1,X2),k2_relset_1(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.10/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f37,f83])).
% 3.10/0.82  fof(f83,plain,(
% 3.10/0.82    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) => (r2_hidden(sK12(X0,X1,X2),k2_relset_1(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),X1)))),
% 3.10/0.82    introduced(choice_axiom,[])).
% 3.10/0.82  fof(f37,plain,(
% 3.10/0.82    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.10/0.82    inference(flattening,[],[f36])).
% 3.10/0.82  fof(f36,plain,(
% 3.10/0.82    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X3,k2_relset_1(X0,X1,X2)) & m1_subset_1(X3,X1)) | k1_xboole_0 = k1_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.10/0.82    inference(ennf_transformation,[],[f25])).
% 3.10/0.82  fof(f25,axiom,(
% 3.10/0.82    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 3.10/0.82  fof(f4333,plain,(
% 3.10/0.82    spl17_32 | ~spl17_136),
% 3.10/0.82    inference(avatar_contradiction_clause,[],[f4332])).
% 3.10/0.82  fof(f4332,plain,(
% 3.10/0.82    $false | (spl17_32 | ~spl17_136)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4317,f120])).
% 3.10/0.82  fof(f120,plain,(
% 3.10/0.82    v1_xboole_0(k1_xboole_0)),
% 3.10/0.82    inference(cnf_transformation,[],[f1])).
% 3.10/0.82  fof(f1,axiom,(
% 3.10/0.82    v1_xboole_0(k1_xboole_0)),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.10/0.82  fof(f4317,plain,(
% 3.10/0.82    ~v1_xboole_0(k1_xboole_0) | (spl17_32 | ~spl17_136)),
% 3.10/0.82    inference(backward_demodulation,[],[f1040,f4312])).
% 3.10/0.82  fof(f4312,plain,(
% 3.10/0.82    k1_xboole_0 = k1_relat_1(sK10) | ~spl17_136),
% 3.10/0.82    inference(avatar_component_clause,[],[f4310])).
% 3.10/0.82  fof(f1040,plain,(
% 3.10/0.82    ~v1_xboole_0(k1_relat_1(sK10)) | spl17_32),
% 3.10/0.82    inference(avatar_component_clause,[],[f1038])).
% 3.10/0.82  fof(f4171,plain,(
% 3.10/0.82    ~spl17_30 | ~spl17_135 | ~spl17_65 | ~spl17_64),
% 3.10/0.82    inference(avatar_split_clause,[],[f4166,f1776,f1781,f4168,f1029])).
% 3.10/0.82  fof(f1029,plain,(
% 3.10/0.82    spl17_30 <=> m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_30])])).
% 3.10/0.82  fof(f4166,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~spl17_64),
% 3.10/0.82    inference(subsumption_resolution,[],[f4165,f110])).
% 3.10/0.82  fof(f4165,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | v1_xboole_0(sK8) | ~spl17_64),
% 3.10/0.82    inference(subsumption_resolution,[],[f4164,f111])).
% 3.10/0.82  fof(f4164,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_1(sK9) | v1_xboole_0(sK8) | ~spl17_64),
% 3.10/0.82    inference(subsumption_resolution,[],[f4163,f112])).
% 3.10/0.82  fof(f4163,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8) | ~spl17_64),
% 3.10/0.82    inference(subsumption_resolution,[],[f4162,f1777])).
% 3.10/0.82  fof(f4162,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4161,f114])).
% 3.10/0.82  fof(f4161,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_1(sK10) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4160,f116])).
% 3.10/0.82  fof(f116,plain,(
% 3.10/0.82    m1_subset_1(sK11,sK7)),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f4160,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK11,sK7) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_1(sK10) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 3.10/0.82    inference(subsumption_resolution,[],[f4159,f118])).
% 3.10/0.82  fof(f4159,plain,(
% 3.10/0.82    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | k1_xboole_0 = sK7 | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK11,sK7) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_1(sK10) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 3.10/0.82    inference(superposition,[],[f119,f162])).
% 3.10/0.82  fof(f162,plain,(
% 3.10/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f55])).
% 3.10/0.82  fof(f55,plain,(
% 3.10/0.82    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.10/0.82    inference(flattening,[],[f54])).
% 3.10/0.82  fof(f54,plain,(
% 3.10/0.82    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.10/0.82    inference(ennf_transformation,[],[f28])).
% 3.10/0.82  fof(f28,axiom,(
% 3.10/0.82    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.10/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 3.10/0.82  fof(f119,plain,(
% 3.10/0.82    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))),
% 3.10/0.82    inference(cnf_transformation,[],[f82])).
% 3.10/0.82  fof(f2533,plain,(
% 3.10/0.82    ~spl17_71 | spl17_73),
% 3.10/0.82    inference(avatar_contradiction_clause,[],[f2532])).
% 3.10/0.82  fof(f2532,plain,(
% 3.10/0.82    $false | (~spl17_71 | spl17_73)),
% 3.10/0.82    inference(subsumption_resolution,[],[f2531,f120])).
% 3.10/0.82  fof(f2531,plain,(
% 3.10/0.82    ~v1_xboole_0(k1_xboole_0) | (~spl17_71 | spl17_73)),
% 3.10/0.82    inference(subsumption_resolution,[],[f2528,f1978])).
% 3.10/0.82  fof(f1978,plain,(
% 3.10/0.82    ~v1_xboole_0(sK9) | spl17_73),
% 3.10/0.82    inference(avatar_component_clause,[],[f1977])).
% 3.10/0.82  fof(f2528,plain,(
% 3.10/0.82    v1_xboole_0(sK9) | ~v1_xboole_0(k1_xboole_0) | ~spl17_71),
% 3.10/0.82    inference(resolution,[],[f712,f2498])).
% 3.10/0.82  fof(f2498,plain,(
% 3.10/0.82    ( ! [X1] : (sP4(X1,k1_xboole_0,sK9)) ) | ~spl17_71),
% 3.10/0.82    inference(subsumption_resolution,[],[f2497,f305])).
% 3.10/0.82  fof(f305,plain,(
% 3.10/0.82    v1_relat_1(sK9)),
% 3.10/0.82    inference(resolution,[],[f163,f113])).
% 3.10/0.82  fof(f2497,plain,(
% 3.10/0.82    ( ! [X1] : (sP4(X1,k1_xboole_0,sK9) | ~v1_relat_1(sK9)) ) | ~spl17_71),
% 3.10/0.82    inference(subsumption_resolution,[],[f2496,f111])).
% 3.10/0.82  fof(f2496,plain,(
% 3.10/0.82    ( ! [X1] : (sP4(X1,k1_xboole_0,sK9) | ~v1_funct_1(sK9) | ~v1_relat_1(sK9)) ) | ~spl17_71),
% 3.10/0.82    inference(subsumption_resolution,[],[f2489,f195])).
% 3.10/0.82  fof(f2489,plain,(
% 3.10/0.82    ( ! [X1] : (r2_hidden(sK16(k1_xboole_0,X1,sK9),k1_xboole_0) | sP4(X1,k1_xboole_0,sK9) | ~v1_funct_1(sK9) | ~v1_relat_1(sK9)) ) | ~spl17_71),
% 3.10/0.82    inference(superposition,[],[f187,f1916])).
% 3.10/0.82  fof(f1916,plain,(
% 3.10/0.82    k1_xboole_0 = k1_relat_1(sK9) | ~spl17_71),
% 3.10/0.82    inference(avatar_component_clause,[],[f1914])).
% 3.10/0.82  fof(f1914,plain,(
% 3.10/0.82    spl17_71 <=> k1_xboole_0 = k1_relat_1(sK9)),
% 3.10/0.82    introduced(avatar_definition,[new_symbols(naming,[spl17_71])])).
% 3.10/0.82  fof(f187,plain,(
% 3.10/0.82    ( ! [X2,X1] : (r2_hidden(sK16(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP4(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.10/0.82    inference(equality_resolution,[],[f170])).
% 3.10/0.82  fof(f170,plain,(
% 3.10/0.82    ( ! [X2,X0,X1] : (sP4(X1,X0,X2) | r2_hidden(sK16(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.10/0.82    inference(cnf_transformation,[],[f107])).
% 3.10/0.82  fof(f107,plain,(
% 3.10/0.82    ! [X0,X1,X2] : (sP4(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK16(X0,X1,X2)),X1) & r2_hidden(sK16(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.10/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f75,f106])).
% 3.10/0.82  fof(f106,plain,(
% 3.10/0.82    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK16(X0,X1,X2)),X1) & r2_hidden(sK16(X0,X1,X2),X0)))),
% 3.10/0.82    introduced(choice_axiom,[])).
% 3.10/0.83  fof(f75,plain,(
% 3.10/0.83    ! [X0,X1,X2] : (sP4(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.10/0.83    inference(definition_folding,[],[f60,f74])).
% 3.10/0.83  fof(f74,plain,(
% 3.10/0.83    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP4(X1,X0,X2))),
% 3.10/0.83    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 3.10/0.83  fof(f60,plain,(
% 3.10/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.10/0.83    inference(flattening,[],[f59])).
% 3.10/0.83  fof(f59,plain,(
% 3.10/0.83    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.10/0.83    inference(ennf_transformation,[],[f29])).
% 3.10/0.83  fof(f29,axiom,(
% 3.10/0.83    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.10/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 3.10/0.83  fof(f712,plain,(
% 3.10/0.83    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | v1_xboole_0(X2) | ~v1_xboole_0(X1)) )),
% 3.10/0.83    inference(resolution,[],[f169,f144])).
% 3.10/0.83  fof(f144,plain,(
% 3.10/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f43])).
% 3.10/0.83  fof(f43,plain,(
% 3.10/0.83    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.10/0.83    inference(ennf_transformation,[],[f23])).
% 3.10/0.83  fof(f23,axiom,(
% 3.10/0.83    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.10/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 3.10/0.83  fof(f169,plain,(
% 3.10/0.83    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP4(X0,X1,X2)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f105])).
% 3.10/0.83  fof(f105,plain,(
% 3.10/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP4(X0,X1,X2))),
% 3.10/0.83    inference(rectify,[],[f104])).
% 3.10/0.83  fof(f104,plain,(
% 3.10/0.83    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP4(X1,X0,X2))),
% 3.10/0.83    inference(nnf_transformation,[],[f74])).
% 3.10/0.83  fof(f1918,plain,(
% 3.10/0.83    ~spl17_64 | spl17_71 | ~spl17_51),
% 3.10/0.83    inference(avatar_split_clause,[],[f1912,f1652,f1914,f1776])).
% 3.10/0.83  fof(f1912,plain,(
% 3.10/0.83    k1_xboole_0 = k1_relat_1(sK9) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~spl17_51),
% 3.10/0.83    inference(superposition,[],[f164,f1654])).
% 3.10/0.83  fof(f1654,plain,(
% 3.10/0.83    k1_xboole_0 = k1_relset_1(sK7,sK8,sK9) | ~spl17_51),
% 3.10/0.83    inference(avatar_component_clause,[],[f1652])).
% 3.10/0.83  fof(f164,plain,(
% 3.10/0.83    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.83    inference(cnf_transformation,[],[f57])).
% 3.10/0.83  fof(f57,plain,(
% 3.10/0.83    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.83    inference(ennf_transformation,[],[f24])).
% 3.10/0.83  fof(f24,axiom,(
% 3.10/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.10/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 3.10/0.83  fof(f1785,plain,(
% 3.10/0.83    spl17_64),
% 3.10/0.83    inference(avatar_split_clause,[],[f113,f1776])).
% 3.10/0.83  fof(f1472,plain,(
% 3.10/0.83    ~spl17_30 | spl17_31),
% 3.10/0.83    inference(avatar_split_clause,[],[f1469,f1033,f1029])).
% 3.10/0.83  fof(f1469,plain,(
% 3.10/0.83    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relat_1(sK10)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 3.10/0.83    inference(superposition,[],[f117,f164])).
% 3.10/0.83  fof(f1434,plain,(
% 3.10/0.83    ~spl17_26),
% 3.10/0.83    inference(avatar_contradiction_clause,[],[f1433])).
% 3.10/0.83  fof(f1433,plain,(
% 3.10/0.83    $false | ~spl17_26),
% 3.10/0.83    inference(subsumption_resolution,[],[f1407,f120])).
% 3.10/0.83  fof(f1407,plain,(
% 3.10/0.83    ~v1_xboole_0(k1_xboole_0) | ~spl17_26),
% 3.10/0.83    inference(backward_demodulation,[],[f110,f932])).
% 3.10/0.83  fof(f932,plain,(
% 3.10/0.83    k1_xboole_0 = sK8 | ~spl17_26),
% 3.10/0.83    inference(avatar_component_clause,[],[f930])).
% 3.10/0.83  fof(f1047,plain,(
% 3.10/0.83    spl17_30),
% 3.10/0.83    inference(avatar_split_clause,[],[f115,f1029])).
% 3.10/0.83  fof(f275,plain,(
% 3.10/0.83    spl17_6 | spl17_7),
% 3.10/0.83    inference(avatar_split_clause,[],[f260,f272,f268])).
% 3.10/0.83  fof(f260,plain,(
% 3.10/0.83    v1_xboole_0(sK7) | r2_hidden(sK11,sK7)),
% 3.10/0.83    inference(resolution,[],[f146,f116])).
% 3.10/0.83  fof(f146,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f46])).
% 3.10/0.83  fof(f46,plain,(
% 3.10/0.83    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.10/0.83    inference(flattening,[],[f45])).
% 3.10/0.83  fof(f45,plain,(
% 3.10/0.83    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.10/0.83    inference(ennf_transformation,[],[f10])).
% 3.10/0.83  fof(f10,axiom,(
% 3.10/0.83    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.10/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 3.10/0.83  % SZS output end Proof for theBenchmark
% 3.10/0.83  % (12297)------------------------------
% 3.10/0.83  % (12297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.83  % (12297)Termination reason: Refutation
% 3.10/0.83  
% 3.10/0.83  % (12297)Memory used [KB]: 8443
% 3.10/0.83  % (12297)Time elapsed: 0.404 s
% 3.10/0.83  % (12297)------------------------------
% 3.10/0.83  % (12297)------------------------------
% 3.10/0.83  % (12292)Success in time 0.463 s
%------------------------------------------------------------------------------
