%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:43 EST 2020

% Result     : Theorem 2.49s
% Output     : Refutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 729 expanded)
%              Number of leaves         :   43 ( 288 expanded)
%              Depth                    :   24
%              Number of atoms          :  808 (5089 expanded)
%              Number of equality atoms :  122 (1175 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f965,f1329,f1824,f1832,f1933,f1942,f1992,f2262,f2347,f2362,f2379,f2706,f2711,f2713,f2721,f2734,f3184,f3190])).

fof(f3190,plain,
    ( ~ spl18_119
    | ~ spl18_121 ),
    inference(avatar_contradiction_clause,[],[f3189])).

fof(f3189,plain,
    ( $false
    | ~ spl18_119
    | ~ spl18_121 ),
    inference(subsumption_resolution,[],[f3188,f112])).

fof(f112,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),sK12) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12))
    & k1_xboole_0 != sK8
    & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11))
    & m1_subset_1(sK12,sK8)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
    & v1_funct_1(sK11)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    & v1_funct_2(sK10,sK8,sK9)
    & v1_funct_1(sK10)
    & ~ v1_xboole_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11,sK12])],[f29,f72,f71,f70,f69])).

fof(f69,plain,
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
                  ( k1_funct_1(k8_funct_2(sK8,sK9,sK7,X3,X4),X5) != k7_partfun1(sK7,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK8
                  & r1_tarski(k2_relset_1(sK8,sK9,X3),k1_relset_1(sK9,sK7,X4))
                  & m1_subset_1(X5,sK8) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
          & v1_funct_2(X3,sK8,sK9)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK8,sK9,sK7,X3,X4),X5) != k7_partfun1(sK7,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK8
                & r1_tarski(k2_relset_1(sK8,sK9,X3),k1_relset_1(sK9,sK7,X4))
                & m1_subset_1(X5,sK8) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
        & v1_funct_2(X3,sK8,sK9)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,X4),X5) != k7_partfun1(sK7,X4,k1_funct_1(sK10,X5))
              & k1_xboole_0 != sK8
              & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,X4))
              & m1_subset_1(X5,sK8) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
      & v1_funct_2(sK10,sK8,sK9)
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,X4),X5) != k7_partfun1(sK7,X4,k1_funct_1(sK10,X5))
            & k1_xboole_0 != sK8
            & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,X4))
            & m1_subset_1(X5,sK8) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),X5) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,X5))
          & k1_xboole_0 != sK8
          & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11))
          & m1_subset_1(X5,sK8) )
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),X5) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,X5))
        & k1_xboole_0 != sK8
        & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11))
        & m1_subset_1(X5,sK8) )
   => ( k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),sK12) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12))
      & k1_xboole_0 != sK8
      & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11))
      & m1_subset_1(sK12,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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

fof(f3188,plain,
    ( k1_xboole_0 = sK8
    | ~ spl18_119
    | ~ spl18_121 ),
    inference(forward_demodulation,[],[f1991,f2011])).

fof(f2011,plain,
    ( k1_xboole_0 = sK10
    | ~ spl18_121 ),
    inference(avatar_component_clause,[],[f2009])).

fof(f2009,plain,
    ( spl18_121
  <=> k1_xboole_0 = sK10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_121])])).

fof(f1991,plain,
    ( sK8 = sK10
    | ~ spl18_119 ),
    inference(avatar_component_clause,[],[f1989])).

fof(f1989,plain,
    ( spl18_119
  <=> sK8 = sK10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_119])])).

fof(f3184,plain,
    ( ~ spl18_4
    | spl18_111
    | ~ spl18_121 ),
    inference(avatar_contradiction_clause,[],[f3183])).

fof(f3183,plain,
    ( $false
    | ~ spl18_4
    | spl18_111
    | ~ spl18_121 ),
    inference(subsumption_resolution,[],[f3179,f225])).

fof(f225,plain,
    ( v1_xboole_0(sK8)
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl18_4
  <=> v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f3179,plain,
    ( ~ v1_xboole_0(sK8)
    | spl18_111
    | ~ spl18_121 ),
    inference(resolution,[],[f2865,f176])).

fof(f176,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2865,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK8,X0)
        | ~ v1_xboole_0(X0) )
    | spl18_111
    | ~ spl18_121 ),
    inference(superposition,[],[f2818,f116])).

fof(f116,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2818,plain,
    ( ~ r1_tarski(sK8,k1_xboole_0)
    | spl18_111
    | ~ spl18_121 ),
    inference(backward_demodulation,[],[f1919,f2011])).

fof(f1919,plain,
    ( ~ r1_tarski(sK8,sK10)
    | spl18_111 ),
    inference(avatar_component_clause,[],[f1917])).

fof(f1917,plain,
    ( spl18_111
  <=> r1_tarski(sK8,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_111])])).

fof(f2734,plain,
    ( spl18_121
    | ~ spl18_69
    | ~ spl18_120 ),
    inference(avatar_split_clause,[],[f2733,f2005,f1322,f2009])).

fof(f1322,plain,
    ( spl18_69
  <=> r1_tarski(sK10,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_69])])).

fof(f2005,plain,
    ( spl18_120
  <=> r1_tarski(k1_xboole_0,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_120])])).

fof(f2733,plain,
    ( k1_xboole_0 = sK10
    | ~ spl18_69
    | ~ spl18_120 ),
    inference(subsumption_resolution,[],[f2729,f1324])).

fof(f1324,plain,
    ( r1_tarski(sK10,k1_xboole_0)
    | ~ spl18_69 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f2729,plain,
    ( k1_xboole_0 = sK10
    | ~ r1_tarski(sK10,k1_xboole_0)
    | ~ spl18_120 ),
    inference(resolution,[],[f2006,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f2006,plain,
    ( r1_tarski(k1_xboole_0,sK10)
    | ~ spl18_120 ),
    inference(avatar_component_clause,[],[f2005])).

fof(f2721,plain,
    ( spl18_9
    | ~ spl18_69 ),
    inference(avatar_split_clause,[],[f2353,f1322,f257])).

fof(f257,plain,
    ( spl18_9
  <=> v1_xboole_0(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).

fof(f2353,plain,
    ( v1_xboole_0(sK10)
    | ~ spl18_69 ),
    inference(subsumption_resolution,[],[f2002,f241])).

fof(f241,plain,(
    ! [X2] : r1_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f142,f184])).

fof(f184,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f140,f178])).

fof(f178,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f140,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f142,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK17(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK17(X0,X1),X1)
          & r2_hidden(sK17(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f39,f93])).

fof(f93,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK17(X0,X1),X1)
        & r2_hidden(sK17(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f2002,plain,
    ( ~ r1_xboole_0(sK10,k1_xboole_0)
    | v1_xboole_0(sK10)
    | ~ spl18_69 ),
    inference(resolution,[],[f1324,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f2713,plain,
    ( ~ spl18_114
    | spl18_53
    | ~ spl18_82 ),
    inference(avatar_split_clause,[],[f2712,f1660,f869,f1939])).

fof(f1939,plain,
    ( spl18_114
  <=> r2_hidden(sK12,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_114])])).

fof(f869,plain,
    ( spl18_53
  <=> k1_xboole_0 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_53])])).

fof(f1660,plain,
    ( spl18_82
  <=> ! [X0] :
        ( ~ r2_hidden(sK12,X0)
        | ~ sP6(k1_relat_1(sK11),X0,sK10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_82])])).

fof(f2712,plain,
    ( ~ r2_hidden(sK12,sK8)
    | spl18_53
    | ~ spl18_82 ),
    inference(subsumption_resolution,[],[f2687,f561])).

fof(f561,plain,(
    r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11)) ),
    inference(subsumption_resolution,[],[f554,f107])).

fof(f107,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f73])).

fof(f554,plain,
    ( r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(superposition,[],[f532,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f532,plain,(
    r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relat_1(sK11)) ),
    inference(subsumption_resolution,[],[f528,f109])).

fof(f109,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) ),
    inference(cnf_transformation,[],[f73])).

fof(f528,plain,
    ( r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relat_1(sK11))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) ),
    inference(superposition,[],[f111,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f111,plain,(
    r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11)) ),
    inference(cnf_transformation,[],[f73])).

fof(f2687,plain,
    ( ~ r2_hidden(sK12,sK8)
    | ~ r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11))
    | spl18_53
    | ~ spl18_82 ),
    inference(resolution,[],[f1661,f1187])).

fof(f1187,plain,
    ( ! [X0] :
        ( sP6(X0,sK8,sK10)
        | ~ r1_tarski(k2_relat_1(sK10),X0) )
    | spl18_53 ),
    inference(subsumption_resolution,[],[f1177,f107])).

fof(f1177,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK10),X0)
        | sP6(X0,sK8,sK10)
        | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) )
    | spl18_53 ),
    inference(superposition,[],[f1132,f162])).

fof(f1132,plain,
    ( ! [X8] :
        ( ~ r1_tarski(k2_relset_1(sK8,sK9,sK10),X8)
        | sP6(X8,sK8,sK10) )
    | spl18_53 ),
    inference(subsumption_resolution,[],[f1131,f105])).

fof(f105,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f73])).

fof(f1131,plain,
    ( ! [X8] :
        ( ~ r1_tarski(k2_relset_1(sK8,sK9,sK10),X8)
        | sP6(X8,sK8,sK10)
        | ~ v1_funct_1(sK10) )
    | spl18_53 ),
    inference(subsumption_resolution,[],[f1130,f106])).

fof(f106,plain,(
    v1_funct_2(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f73])).

fof(f1130,plain,
    ( ! [X8] :
        ( ~ r1_tarski(k2_relset_1(sK8,sK9,sK10),X8)
        | sP6(X8,sK8,sK10)
        | ~ v1_funct_2(sK10,sK8,sK9)
        | ~ v1_funct_1(sK10) )
    | spl18_53 ),
    inference(subsumption_resolution,[],[f1122,f870])).

fof(f870,plain,
    ( k1_xboole_0 != sK9
    | spl18_53 ),
    inference(avatar_component_clause,[],[f869])).

fof(f1122,plain,(
    ! [X8] :
      ( k1_xboole_0 = sK9
      | ~ r1_tarski(k2_relset_1(sK8,sK9,sK10),X8)
      | sP6(X8,sK8,sK10)
      | ~ v1_funct_2(sK10,sK8,sK9)
      | ~ v1_funct_1(sK10) ) ),
    inference(resolution,[],[f169,f107])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | sP6(X2,X0,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( sP6(X2,X0,X3)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_folding,[],[f57,f67])).

fof(f67,plain,(
    ! [X2,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ~ sP6(X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f1661,plain,
    ( ! [X0] :
        ( ~ sP6(k1_relat_1(sK11),X0,sK10)
        | ~ r2_hidden(sK12,X0) )
    | ~ spl18_82 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f2711,plain,
    ( ~ spl18_59
    | spl18_69 ),
    inference(avatar_split_clause,[],[f2417,f1322,f1015])).

fof(f1015,plain,
    ( spl18_59
  <=> v1_xboole_0(k2_zfmisc_1(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_59])])).

fof(f2417,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK8,sK9))
    | spl18_69 ),
    inference(resolution,[],[f2384,f190])).

fof(f190,plain,(
    r1_tarski(sK10,k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[],[f154,f107])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2384,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK10,X0)
        | ~ v1_xboole_0(X0) )
    | spl18_69 ),
    inference(superposition,[],[f1323,f116])).

fof(f1323,plain,
    ( ~ r1_tarski(sK10,k1_xboole_0)
    | spl18_69 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f2706,plain,
    ( ~ spl18_9
    | spl18_69 ),
    inference(avatar_split_clause,[],[f2419,f1322,f257])).

fof(f2419,plain,
    ( ~ v1_xboole_0(sK10)
    | spl18_69 ),
    inference(resolution,[],[f2384,f176])).

fof(f2379,plain,
    ( ~ spl18_9
    | spl18_4 ),
    inference(avatar_split_clause,[],[f773,f224,f257])).

fof(f773,plain,
    ( ~ v1_xboole_0(sK10)
    | spl18_4 ),
    inference(resolution,[],[f759,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X1,X0)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f95])).

fof(f95,plain,(
    ! [X1,X0,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP5(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X1,X0,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & ~ v1_xboole_0(X2)
        & v1_funct_1(X2) )
      | ~ sP5(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f759,plain,
    ( sP5(sK9,sK8,sK10)
    | spl18_4 ),
    inference(subsumption_resolution,[],[f758,f226])).

fof(f226,plain,
    ( ~ v1_xboole_0(sK8)
    | spl18_4 ),
    inference(avatar_component_clause,[],[f224])).

fof(f758,plain,
    ( sP5(sK9,sK8,sK10)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f757,f104])).

fof(f104,plain,(
    ~ v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f73])).

fof(f757,plain,
    ( sP5(sK9,sK8,sK10)
    | v1_xboole_0(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f756,f105])).

fof(f756,plain,
    ( ~ v1_funct_1(sK10)
    | sP5(sK9,sK8,sK10)
    | v1_xboole_0(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f748,f106])).

fof(f748,plain,
    ( ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10)
    | sP5(sK9,sK8,sK10)
    | v1_xboole_0(sK9)
    | v1_xboole_0(sK8) ),
    inference(resolution,[],[f149,f107])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | sP5(X1,X0,X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP5(X1,X0,X2)
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f45,f65])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f2362,plain,
    ( ~ spl18_4
    | spl18_59 ),
    inference(avatar_split_clause,[],[f2340,f1015,f224])).

fof(f2340,plain,
    ( ~ v1_xboole_0(sK8)
    | spl18_59 ),
    inference(duplicate_literal_removal,[],[f1040])).

fof(f1040,plain,
    ( ~ v1_xboole_0(sK8)
    | ~ v1_xboole_0(sK8)
    | spl18_59 ),
    inference(superposition,[],[f1017,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f179,f116])).

fof(f179,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f101])).

fof(f1017,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK8,sK9))
    | spl18_59 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f2347,plain,
    ( ~ spl18_9
    | spl18_120 ),
    inference(avatar_split_clause,[],[f2331,f2005,f257])).

fof(f2331,plain,
    ( ~ v1_xboole_0(sK10)
    | spl18_120 ),
    inference(resolution,[],[f2013,f176])).

fof(f2013,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK10)
        | ~ v1_xboole_0(X0) )
    | spl18_120 ),
    inference(superposition,[],[f2007,f116])).

fof(f2007,plain,
    ( ~ r1_tarski(k1_xboole_0,sK10)
    | spl18_120 ),
    inference(avatar_component_clause,[],[f2005])).

fof(f2262,plain,
    ( spl18_82
    | spl18_81 ),
    inference(avatar_split_clause,[],[f2261,f1656,f1660])).

fof(f1656,plain,
    ( spl18_81
  <=> k1_xboole_0 = k1_relat_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_81])])).

fof(f2261,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK12,X0)
        | ~ sP6(k1_relat_1(sK11),X0,sK10) )
    | spl18_81 ),
    inference(subsumption_resolution,[],[f2258,f1657])).

fof(f1657,plain,
    ( k1_xboole_0 != k1_relat_1(sK11)
    | spl18_81 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f2258,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK12,X0)
      | k1_xboole_0 = k1_relat_1(sK11)
      | ~ sP6(k1_relat_1(sK11),X0,sK10) ) ),
    inference(resolution,[],[f1220,f862])).

fof(f862,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0
      | ~ sP6(X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f861,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | v1_funct_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ~ sP6(X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f861,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ v1_funct_2(X3,X2,X0)
      | ~ sP6(X0,X2,X3) ) ),
    inference(subsumption_resolution,[],[f853,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f853,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k1_funct_1(X3,X1),X0)
      | ~ v1_funct_2(X3,X2,X0)
      | ~ v1_funct_1(X3)
      | ~ sP6(X0,X2,X3) ) ),
    inference(resolution,[],[f165,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f1220,plain,(
    ~ r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11)) ),
    inference(subsumption_resolution,[],[f1219,f333])).

fof(f333,plain,(
    v1_relat_1(sK11) ),
    inference(resolution,[],[f160,f109])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1219,plain,
    ( ~ r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11))
    | ~ v1_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f1218,f428])).

fof(f428,plain,(
    v5_relat_1(sK11,sK7) ),
    inference(resolution,[],[f164,f109])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1218,plain,
    ( ~ r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11))
    | ~ v5_relat_1(sK11,sK7)
    | ~ v1_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f1204,f108])).

fof(f108,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f73])).

fof(f1204,plain,
    ( ~ r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11))
    | ~ v1_funct_1(sK11)
    | ~ v5_relat_1(sK11,sK7)
    | ~ v1_relat_1(sK11) ),
    inference(trivial_inequality_removal,[],[f1203])).

fof(f1203,plain,
    ( k1_funct_1(sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | ~ r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11))
    | ~ v1_funct_1(sK11)
    | ~ v5_relat_1(sK11,sK7)
    | ~ v1_relat_1(sK11) ),
    inference(superposition,[],[f1157,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f1157,plain,(
    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) ),
    inference(subsumption_resolution,[],[f1156,f104])).

fof(f1156,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | v1_xboole_0(sK9) ),
    inference(subsumption_resolution,[],[f1155,f105])).

fof(f1155,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(sK9) ),
    inference(subsumption_resolution,[],[f1154,f106])).

fof(f1154,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(sK9) ),
    inference(subsumption_resolution,[],[f1153,f107])).

fof(f1153,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(sK9) ),
    inference(subsumption_resolution,[],[f1152,f108])).

fof(f1152,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | ~ v1_funct_1(sK11)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(sK9) ),
    inference(subsumption_resolution,[],[f1151,f109])).

fof(f1151,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
    | ~ v1_funct_1(sK11)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(sK9) ),
    inference(subsumption_resolution,[],[f1150,f110])).

fof(f110,plain,(
    m1_subset_1(sK12,sK8) ),
    inference(cnf_transformation,[],[f73])).

fof(f1150,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | ~ m1_subset_1(sK12,sK8)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
    | ~ v1_funct_1(sK11)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(sK9) ),
    inference(subsumption_resolution,[],[f1149,f111])).

fof(f1149,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | ~ r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11))
    | ~ m1_subset_1(sK12,sK8)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
    | ~ v1_funct_1(sK11)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(sK9) ),
    inference(subsumption_resolution,[],[f1143,f112])).

fof(f1143,plain,
    ( k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))
    | k1_xboole_0 = sK8
    | ~ r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11))
    | ~ m1_subset_1(sK12,sK8)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))
    | ~ v1_funct_1(sK11)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10)
    | v1_xboole_0(sK9) ),
    inference(superposition,[],[f113,f159])).

fof(f159,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f113,plain,(
    k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),sK12) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) ),
    inference(cnf_transformation,[],[f73])).

fof(f1992,plain,
    ( ~ spl18_111
    | spl18_119
    | ~ spl18_5 ),
    inference(avatar_split_clause,[],[f1985,f228,f1989,f1917])).

fof(f228,plain,
    ( spl18_5
  <=> r1_tarski(sK10,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f1985,plain,
    ( sK8 = sK10
    | ~ r1_tarski(sK8,sK10)
    | ~ spl18_5 ),
    inference(resolution,[],[f230,f153])).

fof(f230,plain,
    ( r1_tarski(sK10,sK8)
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f228])).

fof(f1942,plain,
    ( spl18_114
    | spl18_4 ),
    inference(avatar_split_clause,[],[f277,f224,f1939])).

fof(f277,plain,
    ( v1_xboole_0(sK8)
    | r2_hidden(sK12,sK8) ),
    inference(resolution,[],[f145,f110])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f1933,plain,
    ( ~ spl18_4
    | spl18_5 ),
    inference(avatar_split_clause,[],[f977,f228,f224])).

fof(f977,plain,
    ( r1_tarski(sK10,sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(superposition,[],[f190,f186])).

fof(f1832,plain,
    ( spl18_9
    | ~ spl18_10 ),
    inference(avatar_split_clause,[],[f976,f261,f257])).

fof(f261,plain,
    ( spl18_10
  <=> r1_xboole_0(sK10,k2_zfmisc_1(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).

fof(f976,plain,
    ( ~ r1_xboole_0(sK10,k2_zfmisc_1(sK8,sK9))
    | v1_xboole_0(sK10) ),
    inference(resolution,[],[f190,f144])).

fof(f1824,plain,
    ( spl18_70
    | ~ spl18_81 ),
    inference(avatar_split_clause,[],[f1687,f1656,f1326])).

fof(f1326,plain,
    ( spl18_70
  <=> r1_tarski(k2_relat_1(sK10),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_70])])).

fof(f1687,plain,
    ( r1_tarski(k2_relat_1(sK10),k1_xboole_0)
    | ~ spl18_81 ),
    inference(backward_demodulation,[],[f561,f1658])).

fof(f1658,plain,
    ( k1_xboole_0 = k1_relat_1(sK11)
    | ~ spl18_81 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f1329,plain,
    ( spl18_69
    | ~ spl18_70
    | spl18_53 ),
    inference(avatar_split_clause,[],[f1319,f869,f1326,f1322])).

fof(f1319,plain,
    ( ~ r1_tarski(k2_relat_1(sK10),k1_xboole_0)
    | r1_tarski(sK10,k1_xboole_0)
    | spl18_53 ),
    inference(resolution,[],[f1187,f511])).

fof(f511,plain,(
    ! [X0,X1] :
      ( ~ sP6(k1_xboole_0,X0,X1)
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f475,f178])).

fof(f475,plain,(
    ! [X14,X12,X13] :
      ( r1_tarski(X14,k2_zfmisc_1(X13,X12))
      | ~ sP6(X12,X13,X14) ) ),
    inference(resolution,[],[f168,f154])).

fof(f965,plain,
    ( spl18_10
    | ~ spl18_53 ),
    inference(avatar_contradiction_clause,[],[f964])).

fof(f964,plain,
    ( $false
    | spl18_10
    | ~ spl18_53 ),
    inference(subsumption_resolution,[],[f963,f114])).

fof(f114,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f963,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl18_10
    | ~ spl18_53 ),
    inference(forward_demodulation,[],[f919,f178])).

fof(f919,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK8,k1_xboole_0))
    | spl18_10
    | ~ spl18_53 ),
    inference(backward_demodulation,[],[f298,f871])).

fof(f871,plain,
    ( k1_xboole_0 = sK9
    | ~ spl18_53 ),
    inference(avatar_component_clause,[],[f869])).

fof(f298,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK8,sK9))
    | spl18_10 ),
    inference(resolution,[],[f263,f240])).

fof(f240,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f142,f134])).

fof(f134,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK15(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f88,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK15(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f263,plain,
    ( ~ r1_xboole_0(sK10,k2_zfmisc_1(sK8,sK9))
    | spl18_10 ),
    inference(avatar_component_clause,[],[f261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:34:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (32455)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (32444)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (32443)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (32448)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (32456)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (32458)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (32450)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (32464)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (32446)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.37/0.54  % (32451)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.37/0.54  % (32445)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.37/0.54  % (32465)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.37/0.54  % (32466)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.37/0.54  % (32447)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.37/0.54  % (32459)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.37/0.54  % (32457)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.37/0.54  % (32460)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.37/0.54  % (32463)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.50/0.55  % (32449)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.50/0.55  % (32462)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.50/0.55  % (32461)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.50/0.55  % (32454)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.50/0.56  % (32452)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.50/0.56  % (32467)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.50/0.56  % (32453)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.50/0.56  % (32468)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.49/0.68  % (32447)Refutation found. Thanks to Tanya!
% 2.49/0.68  % SZS status Theorem for theBenchmark
% 2.49/0.68  % SZS output start Proof for theBenchmark
% 2.49/0.69  fof(f3197,plain,(
% 2.49/0.69    $false),
% 2.49/0.69    inference(avatar_sat_refutation,[],[f965,f1329,f1824,f1832,f1933,f1942,f1992,f2262,f2347,f2362,f2379,f2706,f2711,f2713,f2721,f2734,f3184,f3190])).
% 2.49/0.69  fof(f3190,plain,(
% 2.49/0.69    ~spl18_119 | ~spl18_121),
% 2.49/0.69    inference(avatar_contradiction_clause,[],[f3189])).
% 2.49/0.69  fof(f3189,plain,(
% 2.49/0.69    $false | (~spl18_119 | ~spl18_121)),
% 2.49/0.69    inference(subsumption_resolution,[],[f3188,f112])).
% 2.49/0.69  fof(f112,plain,(
% 2.49/0.69    k1_xboole_0 != sK8),
% 2.49/0.69    inference(cnf_transformation,[],[f73])).
% 2.49/0.69  fof(f73,plain,(
% 2.49/0.69    (((k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),sK12) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) & k1_xboole_0 != sK8 & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11)) & m1_subset_1(sK12,sK8)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) & v1_funct_1(sK11)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10)) & ~v1_xboole_0(sK9)),
% 2.49/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11,sK12])],[f29,f72,f71,f70,f69])).
% 2.49/0.69  fof(f69,plain,(
% 2.49/0.69    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK8,sK9,sK7,X3,X4),X5) != k7_partfun1(sK7,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK8 & r1_tarski(k2_relset_1(sK8,sK9,X3),k1_relset_1(sK9,sK7,X4)) & m1_subset_1(X5,sK8)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(X3,sK8,sK9) & v1_funct_1(X3)) & ~v1_xboole_0(sK9))),
% 2.49/0.69    introduced(choice_axiom,[])).
% 2.49/0.69  fof(f70,plain,(
% 2.49/0.69    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK8,sK9,sK7,X3,X4),X5) != k7_partfun1(sK7,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK8 & r1_tarski(k2_relset_1(sK8,sK9,X3),k1_relset_1(sK9,sK7,X4)) & m1_subset_1(X5,sK8)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(X3,sK8,sK9) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,X4),X5) != k7_partfun1(sK7,X4,k1_funct_1(sK10,X5)) & k1_xboole_0 != sK8 & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,X4)) & m1_subset_1(X5,sK8)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) & v1_funct_1(X4)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10))),
% 2.49/0.69    introduced(choice_axiom,[])).
% 2.49/0.69  fof(f71,plain,(
% 2.49/0.69    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,X4),X5) != k7_partfun1(sK7,X4,k1_funct_1(sK10,X5)) & k1_xboole_0 != sK8 & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,X4)) & m1_subset_1(X5,sK8)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),X5) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,X5)) & k1_xboole_0 != sK8 & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11)) & m1_subset_1(X5,sK8)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) & v1_funct_1(sK11))),
% 2.49/0.69    introduced(choice_axiom,[])).
% 2.49/0.69  fof(f72,plain,(
% 2.49/0.69    ? [X5] : (k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),X5) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,X5)) & k1_xboole_0 != sK8 & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11)) & m1_subset_1(X5,sK8)) => (k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),sK12) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) & k1_xboole_0 != sK8 & r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11)) & m1_subset_1(sK12,sK8))),
% 2.49/0.69    introduced(choice_axiom,[])).
% 2.49/0.69  fof(f29,plain,(
% 2.49/0.69    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.49/0.69    inference(flattening,[],[f28])).
% 2.49/0.69  fof(f28,plain,(
% 2.49/0.69    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.49/0.69    inference(ennf_transformation,[],[f26])).
% 2.49/0.69  fof(f26,negated_conjecture,(
% 2.49/0.69    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.49/0.69    inference(negated_conjecture,[],[f25])).
% 2.49/0.69  fof(f25,conjecture,(
% 2.49/0.69    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 2.49/0.69  fof(f3188,plain,(
% 2.49/0.69    k1_xboole_0 = sK8 | (~spl18_119 | ~spl18_121)),
% 2.49/0.69    inference(forward_demodulation,[],[f1991,f2011])).
% 2.49/0.69  fof(f2011,plain,(
% 2.49/0.69    k1_xboole_0 = sK10 | ~spl18_121),
% 2.49/0.69    inference(avatar_component_clause,[],[f2009])).
% 2.49/0.69  fof(f2009,plain,(
% 2.49/0.69    spl18_121 <=> k1_xboole_0 = sK10),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_121])])).
% 2.49/0.69  fof(f1991,plain,(
% 2.49/0.69    sK8 = sK10 | ~spl18_119),
% 2.49/0.69    inference(avatar_component_clause,[],[f1989])).
% 2.49/0.69  fof(f1989,plain,(
% 2.49/0.69    spl18_119 <=> sK8 = sK10),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_119])])).
% 2.49/0.69  fof(f3184,plain,(
% 2.49/0.69    ~spl18_4 | spl18_111 | ~spl18_121),
% 2.49/0.69    inference(avatar_contradiction_clause,[],[f3183])).
% 2.49/0.69  fof(f3183,plain,(
% 2.49/0.69    $false | (~spl18_4 | spl18_111 | ~spl18_121)),
% 2.49/0.69    inference(subsumption_resolution,[],[f3179,f225])).
% 2.49/0.69  fof(f225,plain,(
% 2.49/0.69    v1_xboole_0(sK8) | ~spl18_4),
% 2.49/0.69    inference(avatar_component_clause,[],[f224])).
% 2.49/0.69  fof(f224,plain,(
% 2.49/0.69    spl18_4 <=> v1_xboole_0(sK8)),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).
% 2.49/0.69  fof(f3179,plain,(
% 2.49/0.69    ~v1_xboole_0(sK8) | (spl18_111 | ~spl18_121)),
% 2.49/0.69    inference(resolution,[],[f2865,f176])).
% 2.49/0.69  fof(f176,plain,(
% 2.49/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.49/0.69    inference(equality_resolution,[],[f152])).
% 2.49/0.69  fof(f152,plain,(
% 2.49/0.69    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.49/0.69    inference(cnf_transformation,[],[f98])).
% 2.49/0.69  fof(f98,plain,(
% 2.49/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.49/0.69    inference(flattening,[],[f97])).
% 2.49/0.69  fof(f97,plain,(
% 2.49/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.49/0.69    inference(nnf_transformation,[],[f5])).
% 2.49/0.69  fof(f5,axiom,(
% 2.49/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.49/0.69  fof(f2865,plain,(
% 2.49/0.69    ( ! [X0] : (~r1_tarski(sK8,X0) | ~v1_xboole_0(X0)) ) | (spl18_111 | ~spl18_121)),
% 2.49/0.69    inference(superposition,[],[f2818,f116])).
% 2.49/0.69  fof(f116,plain,(
% 2.49/0.69    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f31])).
% 2.49/0.69  fof(f31,plain,(
% 2.49/0.69    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.49/0.69    inference(ennf_transformation,[],[f3])).
% 2.49/0.69  fof(f3,axiom,(
% 2.49/0.69    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.49/0.69  fof(f2818,plain,(
% 2.49/0.69    ~r1_tarski(sK8,k1_xboole_0) | (spl18_111 | ~spl18_121)),
% 2.49/0.69    inference(backward_demodulation,[],[f1919,f2011])).
% 2.49/0.69  fof(f1919,plain,(
% 2.49/0.69    ~r1_tarski(sK8,sK10) | spl18_111),
% 2.49/0.69    inference(avatar_component_clause,[],[f1917])).
% 2.49/0.69  fof(f1917,plain,(
% 2.49/0.69    spl18_111 <=> r1_tarski(sK8,sK10)),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_111])])).
% 2.49/0.69  fof(f2734,plain,(
% 2.49/0.69    spl18_121 | ~spl18_69 | ~spl18_120),
% 2.49/0.69    inference(avatar_split_clause,[],[f2733,f2005,f1322,f2009])).
% 2.49/0.69  fof(f1322,plain,(
% 2.49/0.69    spl18_69 <=> r1_tarski(sK10,k1_xboole_0)),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_69])])).
% 2.49/0.69  fof(f2005,plain,(
% 2.49/0.69    spl18_120 <=> r1_tarski(k1_xboole_0,sK10)),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_120])])).
% 2.49/0.69  fof(f2733,plain,(
% 2.49/0.69    k1_xboole_0 = sK10 | (~spl18_69 | ~spl18_120)),
% 2.49/0.69    inference(subsumption_resolution,[],[f2729,f1324])).
% 2.49/0.69  fof(f1324,plain,(
% 2.49/0.69    r1_tarski(sK10,k1_xboole_0) | ~spl18_69),
% 2.49/0.69    inference(avatar_component_clause,[],[f1322])).
% 2.49/0.69  fof(f2729,plain,(
% 2.49/0.69    k1_xboole_0 = sK10 | ~r1_tarski(sK10,k1_xboole_0) | ~spl18_120),
% 2.49/0.69    inference(resolution,[],[f2006,f153])).
% 2.49/0.69  fof(f153,plain,(
% 2.49/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f98])).
% 2.49/0.69  fof(f2006,plain,(
% 2.49/0.69    r1_tarski(k1_xboole_0,sK10) | ~spl18_120),
% 2.49/0.69    inference(avatar_component_clause,[],[f2005])).
% 2.49/0.69  fof(f2721,plain,(
% 2.49/0.69    spl18_9 | ~spl18_69),
% 2.49/0.69    inference(avatar_split_clause,[],[f2353,f1322,f257])).
% 2.49/0.69  fof(f257,plain,(
% 2.49/0.69    spl18_9 <=> v1_xboole_0(sK10)),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).
% 2.49/0.69  fof(f2353,plain,(
% 2.49/0.69    v1_xboole_0(sK10) | ~spl18_69),
% 2.49/0.69    inference(subsumption_resolution,[],[f2002,f241])).
% 2.49/0.69  fof(f241,plain,(
% 2.49/0.69    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) )),
% 2.49/0.69    inference(resolution,[],[f142,f184])).
% 2.49/0.69  fof(f184,plain,(
% 2.49/0.69    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.49/0.69    inference(superposition,[],[f140,f178])).
% 2.49/0.69  fof(f178,plain,(
% 2.49/0.69    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.49/0.69    inference(equality_resolution,[],[f158])).
% 2.49/0.69  fof(f158,plain,(
% 2.49/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.49/0.69    inference(cnf_transformation,[],[f101])).
% 2.49/0.69  fof(f101,plain,(
% 2.49/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.49/0.69    inference(flattening,[],[f100])).
% 2.49/0.69  fof(f100,plain,(
% 2.49/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.49/0.69    inference(nnf_transformation,[],[f7])).
% 2.49/0.69  fof(f7,axiom,(
% 2.49/0.69    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.49/0.69  fof(f140,plain,(
% 2.49/0.69    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.49/0.69    inference(cnf_transformation,[],[f8])).
% 2.49/0.69  fof(f8,axiom,(
% 2.49/0.69    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 2.49/0.69  fof(f142,plain,(
% 2.49/0.69    ( ! [X0,X1] : (r2_hidden(sK17(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f94])).
% 2.49/0.69  fof(f94,plain,(
% 2.49/0.69    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK17(X0,X1),X1) & r2_hidden(sK17(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.49/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f39,f93])).
% 2.49/0.69  fof(f93,plain,(
% 2.49/0.69    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK17(X0,X1),X1) & r2_hidden(sK17(X0,X1),X0)))),
% 2.49/0.69    introduced(choice_axiom,[])).
% 2.49/0.69  fof(f39,plain,(
% 2.49/0.69    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.49/0.69    inference(ennf_transformation,[],[f27])).
% 2.49/0.69  fof(f27,plain,(
% 2.49/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.49/0.69    inference(rectify,[],[f4])).
% 2.49/0.69  fof(f4,axiom,(
% 2.49/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.49/0.69  fof(f2002,plain,(
% 2.49/0.69    ~r1_xboole_0(sK10,k1_xboole_0) | v1_xboole_0(sK10) | ~spl18_69),
% 2.49/0.69    inference(resolution,[],[f1324,f144])).
% 2.49/0.69  fof(f144,plain,(
% 2.49/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f41])).
% 2.49/0.69  fof(f41,plain,(
% 2.49/0.69    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.49/0.69    inference(flattening,[],[f40])).
% 2.49/0.69  fof(f40,plain,(
% 2.49/0.69    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.49/0.69    inference(ennf_transformation,[],[f6])).
% 2.49/0.69  fof(f6,axiom,(
% 2.49/0.69    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.49/0.69  fof(f2713,plain,(
% 2.49/0.69    ~spl18_114 | spl18_53 | ~spl18_82),
% 2.49/0.69    inference(avatar_split_clause,[],[f2712,f1660,f869,f1939])).
% 2.49/0.69  fof(f1939,plain,(
% 2.49/0.69    spl18_114 <=> r2_hidden(sK12,sK8)),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_114])])).
% 2.49/0.69  fof(f869,plain,(
% 2.49/0.69    spl18_53 <=> k1_xboole_0 = sK9),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_53])])).
% 2.49/0.69  fof(f1660,plain,(
% 2.49/0.69    spl18_82 <=> ! [X0] : (~r2_hidden(sK12,X0) | ~sP6(k1_relat_1(sK11),X0,sK10))),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_82])])).
% 2.49/0.69  fof(f2712,plain,(
% 2.49/0.69    ~r2_hidden(sK12,sK8) | (spl18_53 | ~spl18_82)),
% 2.49/0.69    inference(subsumption_resolution,[],[f2687,f561])).
% 2.49/0.69  fof(f561,plain,(
% 2.49/0.69    r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11))),
% 2.49/0.69    inference(subsumption_resolution,[],[f554,f107])).
% 2.49/0.69  fof(f107,plain,(
% 2.49/0.69    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 2.49/0.69    inference(cnf_transformation,[],[f73])).
% 2.49/0.69  fof(f554,plain,(
% 2.49/0.69    r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 2.49/0.69    inference(superposition,[],[f532,f162])).
% 2.49/0.69  fof(f162,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.69    inference(cnf_transformation,[],[f52])).
% 2.49/0.69  fof(f52,plain,(
% 2.49/0.69    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.69    inference(ennf_transformation,[],[f19])).
% 2.49/0.69  fof(f19,axiom,(
% 2.49/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.49/0.69  fof(f532,plain,(
% 2.49/0.69    r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relat_1(sK11))),
% 2.49/0.69    inference(subsumption_resolution,[],[f528,f109])).
% 2.49/0.69  fof(f109,plain,(
% 2.49/0.69    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))),
% 2.49/0.69    inference(cnf_transformation,[],[f73])).
% 2.49/0.69  fof(f528,plain,(
% 2.49/0.69    r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relat_1(sK11)) | ~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7)))),
% 2.49/0.69    inference(superposition,[],[f111,f161])).
% 2.49/0.69  fof(f161,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/0.69    inference(cnf_transformation,[],[f51])).
% 2.49/0.69  fof(f51,plain,(
% 2.49/0.69    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.69    inference(ennf_transformation,[],[f18])).
% 2.49/0.69  fof(f18,axiom,(
% 2.49/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.49/0.69  fof(f111,plain,(
% 2.49/0.69    r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11))),
% 2.49/0.69    inference(cnf_transformation,[],[f73])).
% 2.49/0.69  fof(f2687,plain,(
% 2.49/0.69    ~r2_hidden(sK12,sK8) | ~r1_tarski(k2_relat_1(sK10),k1_relat_1(sK11)) | (spl18_53 | ~spl18_82)),
% 2.49/0.69    inference(resolution,[],[f1661,f1187])).
% 2.49/0.69  fof(f1187,plain,(
% 2.49/0.69    ( ! [X0] : (sP6(X0,sK8,sK10) | ~r1_tarski(k2_relat_1(sK10),X0)) ) | spl18_53),
% 2.49/0.69    inference(subsumption_resolution,[],[f1177,f107])).
% 2.49/0.69  fof(f1177,plain,(
% 2.49/0.69    ( ! [X0] : (~r1_tarski(k2_relat_1(sK10),X0) | sP6(X0,sK8,sK10) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))) ) | spl18_53),
% 2.49/0.69    inference(superposition,[],[f1132,f162])).
% 2.49/0.69  fof(f1132,plain,(
% 2.49/0.69    ( ! [X8] : (~r1_tarski(k2_relset_1(sK8,sK9,sK10),X8) | sP6(X8,sK8,sK10)) ) | spl18_53),
% 2.49/0.69    inference(subsumption_resolution,[],[f1131,f105])).
% 2.49/0.69  fof(f105,plain,(
% 2.49/0.69    v1_funct_1(sK10)),
% 2.49/0.69    inference(cnf_transformation,[],[f73])).
% 2.49/0.69  fof(f1131,plain,(
% 2.49/0.69    ( ! [X8] : (~r1_tarski(k2_relset_1(sK8,sK9,sK10),X8) | sP6(X8,sK8,sK10) | ~v1_funct_1(sK10)) ) | spl18_53),
% 2.49/0.69    inference(subsumption_resolution,[],[f1130,f106])).
% 2.49/0.69  fof(f106,plain,(
% 2.49/0.69    v1_funct_2(sK10,sK8,sK9)),
% 2.49/0.69    inference(cnf_transformation,[],[f73])).
% 2.49/0.69  fof(f1130,plain,(
% 2.49/0.69    ( ! [X8] : (~r1_tarski(k2_relset_1(sK8,sK9,sK10),X8) | sP6(X8,sK8,sK10) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10)) ) | spl18_53),
% 2.49/0.69    inference(subsumption_resolution,[],[f1122,f870])).
% 2.49/0.69  fof(f870,plain,(
% 2.49/0.69    k1_xboole_0 != sK9 | spl18_53),
% 2.49/0.69    inference(avatar_component_clause,[],[f869])).
% 2.49/0.69  fof(f1122,plain,(
% 2.49/0.69    ( ! [X8] : (k1_xboole_0 = sK9 | ~r1_tarski(k2_relset_1(sK8,sK9,sK10),X8) | sP6(X8,sK8,sK10) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10)) )),
% 2.49/0.69    inference(resolution,[],[f169,f107])).
% 2.49/0.69  fof(f169,plain,(
% 2.49/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | sP6(X2,X0,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f68])).
% 2.49/0.69  fof(f68,plain,(
% 2.49/0.69    ! [X0,X1,X2,X3] : (sP6(X2,X0,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.49/0.69    inference(definition_folding,[],[f57,f67])).
% 2.49/0.69  fof(f67,plain,(
% 2.49/0.69    ! [X2,X0,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | ~sP6(X2,X0,X3))),
% 2.49/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 2.49/0.69  fof(f57,plain,(
% 2.49/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.49/0.69    inference(flattening,[],[f56])).
% 2.49/0.69  fof(f56,plain,(
% 2.49/0.69    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.49/0.69    inference(ennf_transformation,[],[f24])).
% 2.49/0.69  fof(f24,axiom,(
% 2.49/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 2.49/0.69  fof(f1661,plain,(
% 2.49/0.69    ( ! [X0] : (~sP6(k1_relat_1(sK11),X0,sK10) | ~r2_hidden(sK12,X0)) ) | ~spl18_82),
% 2.49/0.69    inference(avatar_component_clause,[],[f1660])).
% 2.49/0.69  fof(f2711,plain,(
% 2.49/0.69    ~spl18_59 | spl18_69),
% 2.49/0.69    inference(avatar_split_clause,[],[f2417,f1322,f1015])).
% 2.49/0.69  fof(f1015,plain,(
% 2.49/0.69    spl18_59 <=> v1_xboole_0(k2_zfmisc_1(sK8,sK9))),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_59])])).
% 2.49/0.69  fof(f2417,plain,(
% 2.49/0.69    ~v1_xboole_0(k2_zfmisc_1(sK8,sK9)) | spl18_69),
% 2.49/0.69    inference(resolution,[],[f2384,f190])).
% 2.49/0.69  fof(f190,plain,(
% 2.49/0.69    r1_tarski(sK10,k2_zfmisc_1(sK8,sK9))),
% 2.49/0.69    inference(resolution,[],[f154,f107])).
% 2.49/0.69  fof(f154,plain,(
% 2.49/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f99])).
% 2.49/0.69  fof(f99,plain,(
% 2.49/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.49/0.69    inference(nnf_transformation,[],[f10])).
% 2.49/0.69  fof(f10,axiom,(
% 2.49/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.49/0.69  fof(f2384,plain,(
% 2.49/0.69    ( ! [X0] : (~r1_tarski(sK10,X0) | ~v1_xboole_0(X0)) ) | spl18_69),
% 2.49/0.69    inference(superposition,[],[f1323,f116])).
% 2.49/0.69  fof(f1323,plain,(
% 2.49/0.69    ~r1_tarski(sK10,k1_xboole_0) | spl18_69),
% 2.49/0.69    inference(avatar_component_clause,[],[f1322])).
% 2.49/0.69  fof(f2706,plain,(
% 2.49/0.69    ~spl18_9 | spl18_69),
% 2.49/0.69    inference(avatar_split_clause,[],[f2419,f1322,f257])).
% 2.49/0.69  fof(f2419,plain,(
% 2.49/0.69    ~v1_xboole_0(sK10) | spl18_69),
% 2.49/0.69    inference(resolution,[],[f2384,f176])).
% 2.49/0.69  fof(f2379,plain,(
% 2.49/0.69    ~spl18_9 | spl18_4),
% 2.49/0.69    inference(avatar_split_clause,[],[f773,f224,f257])).
% 2.49/0.69  fof(f773,plain,(
% 2.49/0.69    ~v1_xboole_0(sK10) | spl18_4),
% 2.49/0.69    inference(resolution,[],[f759,f147])).
% 2.49/0.69  fof(f147,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | ~v1_xboole_0(X2)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f96])).
% 2.49/0.69  fof(f96,plain,(
% 2.49/0.69    ! [X0,X1,X2] : ((v1_funct_2(X2,X1,X0) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP5(X0,X1,X2))),
% 2.49/0.69    inference(rectify,[],[f95])).
% 2.49/0.69  fof(f95,plain,(
% 2.49/0.69    ! [X1,X0,X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP5(X1,X0,X2))),
% 2.49/0.69    inference(nnf_transformation,[],[f65])).
% 2.49/0.69  fof(f65,plain,(
% 2.49/0.69    ! [X1,X0,X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~sP5(X1,X0,X2))),
% 2.49/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.49/0.69  fof(f759,plain,(
% 2.49/0.69    sP5(sK9,sK8,sK10) | spl18_4),
% 2.49/0.69    inference(subsumption_resolution,[],[f758,f226])).
% 2.49/0.69  fof(f226,plain,(
% 2.49/0.69    ~v1_xboole_0(sK8) | spl18_4),
% 2.49/0.69    inference(avatar_component_clause,[],[f224])).
% 2.49/0.69  fof(f758,plain,(
% 2.49/0.69    sP5(sK9,sK8,sK10) | v1_xboole_0(sK8)),
% 2.49/0.69    inference(subsumption_resolution,[],[f757,f104])).
% 2.49/0.69  fof(f104,plain,(
% 2.49/0.69    ~v1_xboole_0(sK9)),
% 2.49/0.69    inference(cnf_transformation,[],[f73])).
% 2.49/0.69  fof(f757,plain,(
% 2.49/0.69    sP5(sK9,sK8,sK10) | v1_xboole_0(sK9) | v1_xboole_0(sK8)),
% 2.49/0.69    inference(subsumption_resolution,[],[f756,f105])).
% 2.49/0.69  fof(f756,plain,(
% 2.49/0.69    ~v1_funct_1(sK10) | sP5(sK9,sK8,sK10) | v1_xboole_0(sK9) | v1_xboole_0(sK8)),
% 2.49/0.69    inference(subsumption_resolution,[],[f748,f106])).
% 2.49/0.69  fof(f748,plain,(
% 2.49/0.69    ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10) | sP5(sK9,sK8,sK10) | v1_xboole_0(sK9) | v1_xboole_0(sK8)),
% 2.49/0.69    inference(resolution,[],[f149,f107])).
% 2.49/0.69  fof(f149,plain,(
% 2.49/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | sP5(X1,X0,X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.49/0.69    inference(cnf_transformation,[],[f66])).
% 2.49/0.69  fof(f66,plain,(
% 2.49/0.69    ! [X0,X1] : (! [X2] : (sP5(X1,X0,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.49/0.69    inference(definition_folding,[],[f45,f65])).
% 2.49/0.69  fof(f45,plain,(
% 2.49/0.69    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.49/0.69    inference(flattening,[],[f44])).
% 2.49/0.69  fof(f44,plain,(
% 2.49/0.69    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.49/0.69    inference(ennf_transformation,[],[f20])).
% 2.49/0.69  fof(f20,axiom,(
% 2.49/0.69    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 2.49/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 2.49/0.69  fof(f2362,plain,(
% 2.49/0.69    ~spl18_4 | spl18_59),
% 2.49/0.69    inference(avatar_split_clause,[],[f2340,f1015,f224])).
% 2.49/0.69  fof(f2340,plain,(
% 2.49/0.69    ~v1_xboole_0(sK8) | spl18_59),
% 2.49/0.69    inference(duplicate_literal_removal,[],[f1040])).
% 2.49/0.69  fof(f1040,plain,(
% 2.49/0.69    ~v1_xboole_0(sK8) | ~v1_xboole_0(sK8) | spl18_59),
% 2.49/0.69    inference(superposition,[],[f1017,f186])).
% 2.49/0.69  fof(f186,plain,(
% 2.49/0.69    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 2.49/0.69    inference(superposition,[],[f179,f116])).
% 2.49/0.69  fof(f179,plain,(
% 2.49/0.69    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.49/0.69    inference(equality_resolution,[],[f157])).
% 2.49/0.69  fof(f157,plain,(
% 2.49/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.49/0.69    inference(cnf_transformation,[],[f101])).
% 2.49/0.69  fof(f1017,plain,(
% 2.49/0.69    ~v1_xboole_0(k2_zfmisc_1(sK8,sK9)) | spl18_59),
% 2.49/0.69    inference(avatar_component_clause,[],[f1015])).
% 2.49/0.69  fof(f2347,plain,(
% 2.49/0.69    ~spl18_9 | spl18_120),
% 2.49/0.69    inference(avatar_split_clause,[],[f2331,f2005,f257])).
% 2.49/0.69  fof(f2331,plain,(
% 2.49/0.69    ~v1_xboole_0(sK10) | spl18_120),
% 2.49/0.69    inference(resolution,[],[f2013,f176])).
% 2.49/0.69  fof(f2013,plain,(
% 2.49/0.69    ( ! [X0] : (~r1_tarski(X0,sK10) | ~v1_xboole_0(X0)) ) | spl18_120),
% 2.49/0.69    inference(superposition,[],[f2007,f116])).
% 2.49/0.69  fof(f2007,plain,(
% 2.49/0.69    ~r1_tarski(k1_xboole_0,sK10) | spl18_120),
% 2.49/0.69    inference(avatar_component_clause,[],[f2005])).
% 2.49/0.69  fof(f2262,plain,(
% 2.49/0.69    spl18_82 | spl18_81),
% 2.49/0.69    inference(avatar_split_clause,[],[f2261,f1656,f1660])).
% 2.49/0.69  fof(f1656,plain,(
% 2.49/0.69    spl18_81 <=> k1_xboole_0 = k1_relat_1(sK11)),
% 2.49/0.69    introduced(avatar_definition,[new_symbols(naming,[spl18_81])])).
% 2.49/0.69  fof(f2261,plain,(
% 2.49/0.69    ( ! [X0] : (~r2_hidden(sK12,X0) | ~sP6(k1_relat_1(sK11),X0,sK10)) ) | spl18_81),
% 2.49/0.69    inference(subsumption_resolution,[],[f2258,f1657])).
% 2.49/0.69  fof(f1657,plain,(
% 2.49/0.69    k1_xboole_0 != k1_relat_1(sK11) | spl18_81),
% 2.49/0.69    inference(avatar_component_clause,[],[f1656])).
% 2.49/0.69  fof(f2258,plain,(
% 2.49/0.69    ( ! [X0] : (~r2_hidden(sK12,X0) | k1_xboole_0 = k1_relat_1(sK11) | ~sP6(k1_relat_1(sK11),X0,sK10)) )),
% 2.49/0.69    inference(resolution,[],[f1220,f862])).
% 2.49/0.71  fof(f862,plain,(
% 2.49/0.71    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X1),X0) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0 | ~sP6(X0,X2,X3)) )),
% 2.49/0.71    inference(subsumption_resolution,[],[f861,f167])).
% 2.49/0.71  fof(f167,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (~sP6(X0,X1,X2) | v1_funct_2(X2,X1,X0)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f103])).
% 2.49/0.71  fof(f103,plain,(
% 2.49/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP6(X0,X1,X2))),
% 2.49/0.71    inference(rectify,[],[f102])).
% 2.49/0.71  fof(f102,plain,(
% 2.49/0.71    ! [X2,X0,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | ~sP6(X2,X0,X3))),
% 2.49/0.71    inference(nnf_transformation,[],[f67])).
% 2.49/0.71  fof(f861,plain,(
% 2.49/0.71    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(X3,X1),X0) | ~v1_funct_2(X3,X2,X0) | ~sP6(X0,X2,X3)) )),
% 2.49/0.71    inference(subsumption_resolution,[],[f853,f166])).
% 2.49/0.71  fof(f166,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (~sP6(X0,X1,X2) | v1_funct_1(X2)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f103])).
% 2.49/0.71  fof(f853,plain,(
% 2.49/0.71    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | r2_hidden(k1_funct_1(X3,X1),X0) | ~v1_funct_2(X3,X2,X0) | ~v1_funct_1(X3) | ~sP6(X0,X2,X3)) )),
% 2.49/0.71    inference(resolution,[],[f165,f168])).
% 2.49/0.71  fof(f168,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP6(X0,X1,X2)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f103])).
% 2.49/0.71  fof(f165,plain,(
% 2.49/0.71    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f55])).
% 2.49/0.71  fof(f55,plain,(
% 2.49/0.71    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.49/0.71    inference(flattening,[],[f54])).
% 2.49/0.71  fof(f54,plain,(
% 2.49/0.71    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.49/0.71    inference(ennf_transformation,[],[f23])).
% 2.49/0.71  fof(f23,axiom,(
% 2.49/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.49/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 2.49/0.71  fof(f1220,plain,(
% 2.49/0.71    ~r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11))),
% 2.49/0.71    inference(subsumption_resolution,[],[f1219,f333])).
% 2.49/0.71  fof(f333,plain,(
% 2.49/0.71    v1_relat_1(sK11)),
% 2.49/0.71    inference(resolution,[],[f160,f109])).
% 2.49/0.71  fof(f160,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f50])).
% 2.49/0.71  fof(f50,plain,(
% 2.49/0.71    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.71    inference(ennf_transformation,[],[f16])).
% 2.49/0.71  fof(f16,axiom,(
% 2.49/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.49/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.49/0.71  fof(f1219,plain,(
% 2.49/0.71    ~r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11)) | ~v1_relat_1(sK11)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1218,f428])).
% 2.49/0.71  fof(f428,plain,(
% 2.49/0.71    v5_relat_1(sK11,sK7)),
% 2.49/0.71    inference(resolution,[],[f164,f109])).
% 2.49/0.71  fof(f164,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f53])).
% 2.49/0.71  fof(f53,plain,(
% 2.49/0.71    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/0.71    inference(ennf_transformation,[],[f17])).
% 2.49/0.71  fof(f17,axiom,(
% 2.49/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.49/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.49/0.71  fof(f1218,plain,(
% 2.49/0.71    ~r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11)) | ~v5_relat_1(sK11,sK7) | ~v1_relat_1(sK11)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1204,f108])).
% 2.49/0.71  fof(f108,plain,(
% 2.49/0.71    v1_funct_1(sK11)),
% 2.49/0.71    inference(cnf_transformation,[],[f73])).
% 2.49/0.71  fof(f1204,plain,(
% 2.49/0.71    ~r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11)) | ~v1_funct_1(sK11) | ~v5_relat_1(sK11,sK7) | ~v1_relat_1(sK11)),
% 2.49/0.71    inference(trivial_inequality_removal,[],[f1203])).
% 2.49/0.71  fof(f1203,plain,(
% 2.49/0.71    k1_funct_1(sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | ~r2_hidden(k1_funct_1(sK10,sK12),k1_relat_1(sK11)) | ~v1_funct_1(sK11) | ~v5_relat_1(sK11,sK7) | ~v1_relat_1(sK11)),
% 2.49/0.71    inference(superposition,[],[f1157,f150])).
% 2.49/0.71  fof(f150,plain,(
% 2.49/0.71    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f47])).
% 2.49/0.71  fof(f47,plain,(
% 2.49/0.71    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.49/0.71    inference(flattening,[],[f46])).
% 2.49/0.71  fof(f46,plain,(
% 2.49/0.71    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.49/0.71    inference(ennf_transformation,[],[f21])).
% 2.49/0.71  fof(f21,axiom,(
% 2.49/0.71    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 2.49/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 2.49/0.71  fof(f1157,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12))),
% 2.49/0.71    inference(subsumption_resolution,[],[f1156,f104])).
% 2.49/0.71  fof(f1156,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1155,f105])).
% 2.49/0.71  fof(f1155,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | ~v1_funct_1(sK10) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1154,f106])).
% 2.49/0.71  fof(f1154,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1153,f107])).
% 2.49/0.71  fof(f1153,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1152,f108])).
% 2.49/0.71  fof(f1152,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | ~v1_funct_1(sK11) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1151,f109])).
% 2.49/0.71  fof(f1151,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | ~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) | ~v1_funct_1(sK11) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1150,f110])).
% 2.49/0.71  fof(f110,plain,(
% 2.49/0.71    m1_subset_1(sK12,sK8)),
% 2.49/0.71    inference(cnf_transformation,[],[f73])).
% 2.49/0.71  fof(f1150,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | ~m1_subset_1(sK12,sK8) | ~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) | ~v1_funct_1(sK11) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1149,f111])).
% 2.49/0.71  fof(f1149,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | ~r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11)) | ~m1_subset_1(sK12,sK8) | ~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) | ~v1_funct_1(sK11) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(subsumption_resolution,[],[f1143,f112])).
% 2.49/0.71  fof(f1143,plain,(
% 2.49/0.71    k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12)) != k1_funct_1(sK11,k1_funct_1(sK10,sK12)) | k1_xboole_0 = sK8 | ~r1_tarski(k2_relset_1(sK8,sK9,sK10),k1_relset_1(sK9,sK7,sK11)) | ~m1_subset_1(sK12,sK8) | ~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK7))) | ~v1_funct_1(sK11) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10) | v1_xboole_0(sK9)),
% 2.49/0.71    inference(superposition,[],[f113,f159])).
% 2.49/0.71  fof(f159,plain,(
% 2.49/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f49])).
% 2.49/0.71  fof(f49,plain,(
% 2.49/0.71    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.49/0.71    inference(flattening,[],[f48])).
% 2.49/0.71  fof(f48,plain,(
% 2.49/0.71    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.49/0.71    inference(ennf_transformation,[],[f22])).
% 2.49/0.71  fof(f22,axiom,(
% 2.49/0.71    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.49/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 2.49/0.71  fof(f113,plain,(
% 2.49/0.71    k1_funct_1(k8_funct_2(sK8,sK9,sK7,sK10,sK11),sK12) != k7_partfun1(sK7,sK11,k1_funct_1(sK10,sK12))),
% 2.49/0.71    inference(cnf_transformation,[],[f73])).
% 2.49/0.71  fof(f1992,plain,(
% 2.49/0.71    ~spl18_111 | spl18_119 | ~spl18_5),
% 2.49/0.71    inference(avatar_split_clause,[],[f1985,f228,f1989,f1917])).
% 2.49/0.71  fof(f228,plain,(
% 2.49/0.71    spl18_5 <=> r1_tarski(sK10,sK8)),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).
% 2.49/0.71  fof(f1985,plain,(
% 2.49/0.71    sK8 = sK10 | ~r1_tarski(sK8,sK10) | ~spl18_5),
% 2.49/0.71    inference(resolution,[],[f230,f153])).
% 2.49/0.71  fof(f230,plain,(
% 2.49/0.71    r1_tarski(sK10,sK8) | ~spl18_5),
% 2.49/0.71    inference(avatar_component_clause,[],[f228])).
% 2.49/0.71  fof(f1942,plain,(
% 2.49/0.71    spl18_114 | spl18_4),
% 2.49/0.71    inference(avatar_split_clause,[],[f277,f224,f1939])).
% 2.49/0.71  fof(f277,plain,(
% 2.49/0.71    v1_xboole_0(sK8) | r2_hidden(sK12,sK8)),
% 2.49/0.71    inference(resolution,[],[f145,f110])).
% 2.49/0.71  fof(f145,plain,(
% 2.49/0.71    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f43])).
% 2.49/0.71  fof(f43,plain,(
% 2.49/0.71    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.49/0.71    inference(flattening,[],[f42])).
% 2.49/0.71  fof(f42,plain,(
% 2.49/0.71    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.49/0.71    inference(ennf_transformation,[],[f9])).
% 2.49/0.71  fof(f9,axiom,(
% 2.49/0.71    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.49/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.49/0.71  fof(f1933,plain,(
% 2.49/0.71    ~spl18_4 | spl18_5),
% 2.49/0.71    inference(avatar_split_clause,[],[f977,f228,f224])).
% 2.49/0.71  fof(f977,plain,(
% 2.49/0.71    r1_tarski(sK10,sK8) | ~v1_xboole_0(sK8)),
% 2.49/0.71    inference(superposition,[],[f190,f186])).
% 2.49/0.71  fof(f1832,plain,(
% 2.49/0.71    spl18_9 | ~spl18_10),
% 2.49/0.71    inference(avatar_split_clause,[],[f976,f261,f257])).
% 2.49/0.71  fof(f261,plain,(
% 2.49/0.71    spl18_10 <=> r1_xboole_0(sK10,k2_zfmisc_1(sK8,sK9))),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).
% 2.49/0.71  fof(f976,plain,(
% 2.49/0.71    ~r1_xboole_0(sK10,k2_zfmisc_1(sK8,sK9)) | v1_xboole_0(sK10)),
% 2.49/0.71    inference(resolution,[],[f190,f144])).
% 2.49/0.71  fof(f1824,plain,(
% 2.49/0.71    spl18_70 | ~spl18_81),
% 2.49/0.71    inference(avatar_split_clause,[],[f1687,f1656,f1326])).
% 2.49/0.71  fof(f1326,plain,(
% 2.49/0.71    spl18_70 <=> r1_tarski(k2_relat_1(sK10),k1_xboole_0)),
% 2.49/0.71    introduced(avatar_definition,[new_symbols(naming,[spl18_70])])).
% 2.49/0.71  fof(f1687,plain,(
% 2.49/0.71    r1_tarski(k2_relat_1(sK10),k1_xboole_0) | ~spl18_81),
% 2.49/0.71    inference(backward_demodulation,[],[f561,f1658])).
% 2.49/0.71  fof(f1658,plain,(
% 2.49/0.71    k1_xboole_0 = k1_relat_1(sK11) | ~spl18_81),
% 2.49/0.71    inference(avatar_component_clause,[],[f1656])).
% 2.49/0.71  fof(f1329,plain,(
% 2.49/0.71    spl18_69 | ~spl18_70 | spl18_53),
% 2.49/0.71    inference(avatar_split_clause,[],[f1319,f869,f1326,f1322])).
% 2.49/0.71  fof(f1319,plain,(
% 2.49/0.71    ~r1_tarski(k2_relat_1(sK10),k1_xboole_0) | r1_tarski(sK10,k1_xboole_0) | spl18_53),
% 2.49/0.71    inference(resolution,[],[f1187,f511])).
% 2.49/0.71  fof(f511,plain,(
% 2.49/0.71    ( ! [X0,X1] : (~sP6(k1_xboole_0,X0,X1) | r1_tarski(X1,k1_xboole_0)) )),
% 2.49/0.71    inference(superposition,[],[f475,f178])).
% 2.49/0.71  fof(f475,plain,(
% 2.49/0.71    ( ! [X14,X12,X13] : (r1_tarski(X14,k2_zfmisc_1(X13,X12)) | ~sP6(X12,X13,X14)) )),
% 2.49/0.71    inference(resolution,[],[f168,f154])).
% 2.49/0.71  fof(f965,plain,(
% 2.49/0.71    spl18_10 | ~spl18_53),
% 2.49/0.71    inference(avatar_contradiction_clause,[],[f964])).
% 2.49/0.71  fof(f964,plain,(
% 2.49/0.71    $false | (spl18_10 | ~spl18_53)),
% 2.49/0.71    inference(subsumption_resolution,[],[f963,f114])).
% 2.49/0.71  fof(f114,plain,(
% 2.49/0.71    v1_xboole_0(k1_xboole_0)),
% 2.49/0.71    inference(cnf_transformation,[],[f2])).
% 2.49/0.71  fof(f2,axiom,(
% 2.49/0.71    v1_xboole_0(k1_xboole_0)),
% 2.49/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.49/0.71  fof(f963,plain,(
% 2.49/0.71    ~v1_xboole_0(k1_xboole_0) | (spl18_10 | ~spl18_53)),
% 2.49/0.71    inference(forward_demodulation,[],[f919,f178])).
% 2.49/0.71  fof(f919,plain,(
% 2.49/0.71    ~v1_xboole_0(k2_zfmisc_1(sK8,k1_xboole_0)) | (spl18_10 | ~spl18_53)),
% 2.49/0.71    inference(backward_demodulation,[],[f298,f871])).
% 2.49/0.71  fof(f871,plain,(
% 2.49/0.71    k1_xboole_0 = sK9 | ~spl18_53),
% 2.49/0.71    inference(avatar_component_clause,[],[f869])).
% 2.49/0.71  fof(f298,plain,(
% 2.49/0.71    ~v1_xboole_0(k2_zfmisc_1(sK8,sK9)) | spl18_10),
% 2.49/0.71    inference(resolution,[],[f263,f240])).
% 2.49/0.71  fof(f240,plain,(
% 2.49/0.71    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X1)) )),
% 2.49/0.71    inference(resolution,[],[f142,f134])).
% 2.49/0.71  fof(f134,plain,(
% 2.49/0.71    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.49/0.71    inference(cnf_transformation,[],[f90])).
% 2.49/0.71  fof(f90,plain,(
% 2.49/0.71    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK15(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.49/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f88,f89])).
% 2.49/0.71  fof(f89,plain,(
% 2.49/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK15(X0),X0))),
% 2.49/0.71    introduced(choice_axiom,[])).
% 2.49/0.71  fof(f88,plain,(
% 2.49/0.71    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.49/0.71    inference(rectify,[],[f87])).
% 2.49/0.71  fof(f87,plain,(
% 2.49/0.71    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.49/0.71    inference(nnf_transformation,[],[f1])).
% 2.49/0.71  fof(f1,axiom,(
% 2.49/0.71    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.49/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.49/0.71  fof(f263,plain,(
% 2.49/0.71    ~r1_xboole_0(sK10,k2_zfmisc_1(sK8,sK9)) | spl18_10),
% 2.49/0.71    inference(avatar_component_clause,[],[f261])).
% 2.49/0.71  % SZS output end Proof for theBenchmark
% 2.49/0.71  % (32447)------------------------------
% 2.49/0.71  % (32447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.49/0.71  % (32447)Termination reason: Refutation
% 2.49/0.71  
% 2.49/0.71  % (32447)Memory used [KB]: 7547
% 2.49/0.71  % (32447)Time elapsed: 0.258 s
% 2.49/0.71  % (32447)------------------------------
% 2.49/0.71  % (32447)------------------------------
% 2.49/0.71  % (32438)Success in time 0.348 s
%------------------------------------------------------------------------------
