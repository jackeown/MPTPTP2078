%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:37 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 645 expanded)
%              Number of leaves         :   35 ( 249 expanded)
%              Depth                    :   16
%              Number of atoms          :  735 (4174 expanded)
%              Number of equality atoms :  164 (1032 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f599,f957,f1469,f2409,f3286,f3297,f4155,f4164,f4239,f5169,f5184,f5248])).

fof(f5248,plain,
    ( spl11_114
    | ~ spl11_87 ),
    inference(avatar_split_clause,[],[f3094,f3090,f4148])).

fof(f4148,plain,
    ( spl11_114
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_114])])).

fof(f3090,plain,
    ( spl11_87
  <=> sP1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).

fof(f3094,plain,
    ( k1_xboole_0 = sK6
    | ~ spl11_87 ),
    inference(resolution,[],[f3092,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f3092,plain,
    ( sP1(sK5,sK6)
    | ~ spl11_87 ),
    inference(avatar_component_clause,[],[f3090])).

fof(f5184,plain,
    ( spl11_26
    | ~ spl11_175 ),
    inference(avatar_split_clause,[],[f5170,f5165,f593])).

fof(f593,plain,
    ( spl11_26
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f5165,plain,
    ( spl11_175
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_175])])).

fof(f5170,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl11_175 ),
    inference(backward_demodulation,[],[f75,f5167])).

fof(f5167,plain,
    ( k1_xboole_0 = sK7
    | ~ spl11_175 ),
    inference(avatar_component_clause,[],[f5165])).

fof(f75,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    & k1_xboole_0 != sK5
    & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f24,f58,f57,f56,f55])).

fof(f55,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
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
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5)
                  & k1_xboole_0 != sK5
                  & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4))
                  & m1_subset_1(X5,sK5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5)
                & k1_xboole_0 != sK5
                & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4))
                & m1_subset_1(X5,sK5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X3,sK5,sK6)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,X4),X5) != k1_funct_1(X4,k1_funct_1(sK7,X5))
              & k1_xboole_0 != sK5
              & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,X4))
              & m1_subset_1(X5,sK5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,X4),X5) != k1_funct_1(X4,k1_funct_1(sK7,X5))
            & k1_xboole_0 != sK5
            & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,X4))
            & m1_subset_1(X5,sK5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X5) != k1_funct_1(sK8,k1_funct_1(sK7,X5))
          & k1_xboole_0 != sK5
          & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
          & m1_subset_1(X5,sK5) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X5) != k1_funct_1(sK8,k1_funct_1(sK7,X5))
        & k1_xboole_0 != sK5
        & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
        & m1_subset_1(X5,sK5) )
   => ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
      & k1_xboole_0 != sK5
      & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
      & m1_subset_1(sK9,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f5169,plain,
    ( spl11_175
    | ~ spl11_114 ),
    inference(avatar_split_clause,[],[f5161,f4148,f5165])).

fof(f5161,plain,
    ( k1_xboole_0 = sK7
    | ~ spl11_114 ),
    inference(subsumption_resolution,[],[f5160,f82])).

fof(f82,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f59])).

fof(f5160,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl11_114 ),
    inference(subsumption_resolution,[],[f5157,f4166])).

fof(f4166,plain,
    ( v1_funct_2(sK7,sK5,k1_xboole_0)
    | ~ spl11_114 ),
    inference(backward_demodulation,[],[f76,f4150])).

fof(f4150,plain,
    ( k1_xboole_0 = sK6
    | ~ spl11_114 ),
    inference(avatar_component_clause,[],[f4148])).

fof(f76,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f5157,plain,
    ( ~ v1_funct_2(sK7,sK5,k1_xboole_0)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl11_114 ),
    inference(resolution,[],[f4187,f128])).

fof(f128,plain,(
    ! [X2,X0] :
      ( ~ sP3(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f4187,plain,
    ( sP3(sK7,k1_xboole_0,sK5)
    | ~ spl11_114 ),
    inference(backward_demodulation,[],[f330,f4150])).

fof(f330,plain,(
    sP3(sK7,sK6,sK5) ),
    inference(resolution,[],[f117,f77])).

fof(f77,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f59])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f40,f53,f52,f51])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f4239,plain,
    ( ~ spl11_2
    | ~ spl11_114 ),
    inference(avatar_split_clause,[],[f4165,f4148,f162])).

fof(f162,plain,
    ( spl11_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f4165,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl11_114 ),
    inference(backward_demodulation,[],[f74,f4150])).

fof(f74,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f4164,plain,
    ( ~ spl11_7
    | spl11_87
    | spl11_115 ),
    inference(avatar_contradiction_clause,[],[f4163])).

fof(f4163,plain,
    ( $false
    | ~ spl11_7
    | spl11_87
    | spl11_115 ),
    inference(subsumption_resolution,[],[f4162,f198])).

fof(f198,plain,
    ( r2_hidden(sK9,sK5)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl11_7
  <=> r2_hidden(sK9,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f4162,plain,
    ( ~ r2_hidden(sK9,sK5)
    | spl11_87
    | spl11_115 ),
    inference(forward_demodulation,[],[f4161,f3187])).

fof(f3187,plain,
    ( sK5 = k1_relat_1(sK7)
    | spl11_87 ),
    inference(subsumption_resolution,[],[f3186,f3091])).

fof(f3091,plain,
    ( ~ sP1(sK5,sK6)
    | spl11_87 ),
    inference(avatar_component_clause,[],[f3090])).

fof(f3186,plain,
    ( sP1(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f3180,f76])).

fof(f3180,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP1(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(resolution,[],[f77,f659])).

fof(f659,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f654,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f654,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f112,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f4161,plain,
    ( ~ r2_hidden(sK9,k1_relat_1(sK7))
    | spl11_115 ),
    inference(subsumption_resolution,[],[f4160,f212])).

fof(f212,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f106,f77])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f4160,plain,
    ( ~ r2_hidden(sK9,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | spl11_115 ),
    inference(subsumption_resolution,[],[f4159,f75])).

fof(f4159,plain,
    ( ~ r2_hidden(sK9,k1_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl11_115 ),
    inference(subsumption_resolution,[],[f4158,f213])).

fof(f213,plain,(
    v1_relat_1(sK8) ),
    inference(resolution,[],[f106,f79])).

fof(f79,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f4158,plain,
    ( ~ r2_hidden(sK9,k1_relat_1(sK7))
    | ~ v1_relat_1(sK8)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl11_115 ),
    inference(subsumption_resolution,[],[f4157,f78])).

fof(f78,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f4157,plain,
    ( ~ r2_hidden(sK9,k1_relat_1(sK7))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl11_115 ),
    inference(trivial_inequality_removal,[],[f4156])).

fof(f4156,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r2_hidden(sK9,k1_relat_1(sK7))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl11_115 ),
    inference(superposition,[],[f4154,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f4154,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | spl11_115 ),
    inference(avatar_component_clause,[],[f4152])).

fof(f4152,plain,
    ( spl11_115
  <=> k1_funct_1(sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k5_relat_1(sK7,sK8),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_115])])).

fof(f4155,plain,
    ( spl11_114
    | ~ spl11_115 ),
    inference(avatar_split_clause,[],[f4146,f4152,f4148])).

fof(f4146,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f4145,f76])).

fof(f4145,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | k1_xboole_0 = sK6
    | ~ v1_funct_2(sK7,sK5,sK6) ),
    inference(subsumption_resolution,[],[f4144,f81])).

fof(f81,plain,(
    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f59])).

fof(f4144,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | k1_xboole_0 = sK6
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_2(sK7,sK5,sK6) ),
    inference(subsumption_resolution,[],[f4143,f75])).

fof(f4143,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | ~ v1_funct_1(sK7)
    | k1_xboole_0 = sK6
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_2(sK7,sK5,sK6) ),
    inference(subsumption_resolution,[],[f4142,f77])).

fof(f4142,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | k1_xboole_0 = sK6
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_2(sK7,sK5,sK6) ),
    inference(subsumption_resolution,[],[f4141,f78])).

fof(f4141,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | k1_xboole_0 = sK6
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_2(sK7,sK5,sK6) ),
    inference(subsumption_resolution,[],[f4140,f79])).

fof(f4140,plain,
    ( k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7)
    | k1_xboole_0 = sK6
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_2(sK7,sK5,sK6) ),
    inference(superposition,[],[f83,f847])).

fof(f847,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k5_relat_1(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ v1_funct_2(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f846])).

fof(f846,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k5_relat_1(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f122,f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f83,plain,(
    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f59])).

fof(f3297,plain,
    ( ~ spl11_8
    | spl11_87
    | spl11_90 ),
    inference(avatar_split_clause,[],[f3294,f3247,f3090,f200])).

fof(f200,plain,
    ( spl11_8
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f3247,plain,
    ( spl11_90
  <=> v4_relat_1(sK7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f3294,plain,
    ( ~ v1_xboole_0(sK5)
    | spl11_87
    | spl11_90 ),
    inference(forward_demodulation,[],[f3293,f3187])).

fof(f3293,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK7))
    | spl11_90 ),
    inference(subsumption_resolution,[],[f3287,f212])).

fof(f3287,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_xboole_0(k1_relat_1(sK7))
    | spl11_90 ),
    inference(resolution,[],[f3249,f239])).

fof(f239,plain,(
    ! [X4,X3] :
      ( v4_relat_1(X3,X4)
      | ~ v1_relat_1(X3)
      | ~ v1_xboole_0(k1_relat_1(X3)) ) ),
    inference(resolution,[],[f91,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f104,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f85,f86])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f3249,plain,
    ( ~ v4_relat_1(sK7,k1_xboole_0)
    | spl11_90 ),
    inference(avatar_component_clause,[],[f3247])).

fof(f3286,plain,
    ( ~ spl11_90
    | spl11_87 ),
    inference(avatar_split_clause,[],[f3244,f3090,f3247])).

fof(f3244,plain,
    ( ~ v4_relat_1(sK7,k1_xboole_0)
    | spl11_87 ),
    inference(subsumption_resolution,[],[f3243,f212])).

fof(f3243,plain,
    ( ~ v4_relat_1(sK7,k1_xboole_0)
    | ~ v1_relat_1(sK7)
    | spl11_87 ),
    inference(subsumption_resolution,[],[f3210,f82])).

fof(f3210,plain,
    ( k1_xboole_0 = sK5
    | ~ v4_relat_1(sK7,k1_xboole_0)
    | ~ v1_relat_1(sK7)
    | spl11_87 ),
    inference(superposition,[],[f289,f3187])).

fof(f289,plain,(
    ! [X1] :
      ( k1_xboole_0 = k1_relat_1(X1)
      | ~ v4_relat_1(X1,k1_xboole_0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f251,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f251,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f97,f142])).

fof(f142,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f104,f85])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2409,plain,
    ( spl11_7
    | spl11_8 ),
    inference(avatar_split_clause,[],[f409,f200,f196])).

fof(f409,plain,
    ( v1_xboole_0(sK5)
    | r2_hidden(sK9,sK5) ),
    inference(resolution,[],[f92,f80])).

fof(f80,plain,(
    m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1469,plain,
    ( ~ spl11_26
    | ~ spl11_27
    | ~ spl11_48 ),
    inference(avatar_contradiction_clause,[],[f1468])).

fof(f1468,plain,
    ( $false
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1329,f1258])).

fof(f1258,plain,
    ( ! [X2] : k1_xboole_0 = X2
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_48 ),
    inference(subsumption_resolution,[],[f1257,f956])).

fof(f956,plain,
    ( ! [X0] :
        ( v1_partfun1(k1_xboole_0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f955])).

fof(f955,plain,
    ( spl11_48
  <=> ! [X0] :
        ( v1_partfun1(k1_xboole_0,X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f1257,plain,
    ( ! [X2] :
        ( ~ v1_partfun1(k1_xboole_0,X2)
        | k1_xboole_0 = X2 )
    | ~ spl11_26
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f1256,f211])).

fof(f211,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f106,f85])).

fof(f1256,plain,
    ( ! [X2] :
        ( k1_xboole_0 = X2
        | ~ v1_partfun1(k1_xboole_0,X2)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl11_26
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f1245,f308])).

fof(f308,plain,(
    ! [X5] : v4_relat_1(k1_xboole_0,X5) ),
    inference(resolution,[],[f108,f85])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1245,plain,
    ( ! [X2] :
        ( k1_xboole_0 = X2
        | ~ v1_partfun1(k1_xboole_0,X2)
        | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl11_26
    | ~ spl11_27 ),
    inference(superposition,[],[f1238,f289])).

fof(f1238,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = X0
        | ~ v1_partfun1(k1_xboole_0,X0) )
    | ~ spl11_26
    | ~ spl11_27 ),
    inference(resolution,[],[f1235,f598])).

fof(f598,plain,
    ( ! [X14,X13] :
        ( v1_funct_2(k1_xboole_0,X13,X14)
        | ~ v1_partfun1(k1_xboole_0,X13) )
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl11_27
  <=> ! [X13,X14] :
        ( ~ v1_partfun1(k1_xboole_0,X13)
        | v1_funct_2(k1_xboole_0,X13,X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f1235,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(k1_xboole_0,X1,X1)
        | k1_relat_1(k1_xboole_0) = X1 )
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f1232,f85])).

fof(f1232,plain,
    ( ! [X1] :
        ( k1_relat_1(k1_xboole_0) = X1
        | ~ v1_funct_2(k1_xboole_0,X1,X1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
    | ~ spl11_26 ),
    inference(superposition,[],[f752,f107])).

fof(f752,plain,
    ( ! [X15] :
        ( k1_relset_1(X15,X15,k1_xboole_0) = X15
        | ~ v1_funct_2(k1_xboole_0,X15,X15) )
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f749,f594])).

fof(f594,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f593])).

fof(f749,plain,(
    ! [X15] :
      ( k1_relset_1(X15,X15,k1_xboole_0) = X15
      | ~ v1_funct_2(k1_xboole_0,X15,X15)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[],[f94,f85])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f1329,plain,
    ( k1_xboole_0 != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_48 ),
    inference(backward_demodulation,[],[f83,f1258])).

fof(f957,plain,
    ( spl11_2
    | spl11_48
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f912,f593,f955,f162])).

fof(f912,plain,
    ( ! [X0] :
        ( v1_partfun1(k1_xboole_0,X0)
        | v1_xboole_0(k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl11_26 ),
    inference(resolution,[],[f626,f363])).

fof(f363,plain,(
    ! [X2] :
      ( v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f127,f329])).

fof(f329,plain,(
    ! [X6,X7] : sP3(k1_xboole_0,X6,X7) ),
    inference(resolution,[],[f117,f85])).

fof(f127,plain,(
    ! [X2] :
      ( v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ sP3(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k1_xboole_0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X2,X1)
      | k1_xboole_0 != X0
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f626,plain,
    ( ! [X14,X13] :
        ( ~ v1_funct_2(k1_xboole_0,X13,X14)
        | v1_partfun1(k1_xboole_0,X13)
        | v1_xboole_0(X14) )
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f621,f594])).

fof(f621,plain,(
    ! [X14,X13] :
      ( ~ v1_funct_2(k1_xboole_0,X13,X14)
      | ~ v1_funct_1(k1_xboole_0)
      | v1_partfun1(k1_xboole_0,X13)
      | v1_xboole_0(X14) ) ),
    inference(resolution,[],[f89,f85])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f599,plain,
    ( ~ spl11_26
    | spl11_27 ),
    inference(avatar_split_clause,[],[f588,f597,f593])).

fof(f588,plain,(
    ! [X14,X13] :
      ( ~ v1_partfun1(k1_xboole_0,X13)
      | ~ v1_funct_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,X13,X14) ) ),
    inference(resolution,[],[f119,f85])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 17:40:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.50  % (28795)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (28791)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (28796)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (28797)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (28801)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (28793)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (28815)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (28807)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (28803)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (28810)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (28798)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (28792)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (28813)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (28797)Refutation not found, incomplete strategy% (28797)------------------------------
% 0.22/0.52  % (28797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28797)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28797)Memory used [KB]: 10746
% 0.22/0.52  % (28797)Time elapsed: 0.101 s
% 0.22/0.52  % (28797)------------------------------
% 0.22/0.52  % (28797)------------------------------
% 0.22/0.52  % (28817)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (28802)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (28799)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (28800)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (28804)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (28816)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (28794)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (28814)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (28792)Refutation not found, incomplete strategy% (28792)------------------------------
% 0.22/0.53  % (28792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28792)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28792)Memory used [KB]: 10746
% 0.22/0.53  % (28792)Time elapsed: 0.112 s
% 0.22/0.53  % (28792)------------------------------
% 0.22/0.53  % (28792)------------------------------
% 0.22/0.53  % (28805)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (28809)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (28812)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (28808)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (28811)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 2.28/0.67  % (28800)Refutation not found, incomplete strategy% (28800)------------------------------
% 2.28/0.67  % (28800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.68  % (28800)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.68  
% 2.28/0.68  % (28800)Memory used [KB]: 6396
% 2.28/0.68  % (28800)Time elapsed: 0.238 s
% 2.28/0.68  % (28800)------------------------------
% 2.28/0.68  % (28800)------------------------------
% 2.28/0.72  % (28795)Refutation found. Thanks to Tanya!
% 2.28/0.72  % SZS status Theorem for theBenchmark
% 2.84/0.72  % SZS output start Proof for theBenchmark
% 2.84/0.72  fof(f5249,plain,(
% 2.84/0.72    $false),
% 2.84/0.72    inference(avatar_sat_refutation,[],[f599,f957,f1469,f2409,f3286,f3297,f4155,f4164,f4239,f5169,f5184,f5248])).
% 2.84/0.72  fof(f5248,plain,(
% 2.84/0.72    spl11_114 | ~spl11_87),
% 2.84/0.72    inference(avatar_split_clause,[],[f3094,f3090,f4148])).
% 2.84/0.72  fof(f4148,plain,(
% 2.84/0.72    spl11_114 <=> k1_xboole_0 = sK6),
% 2.84/0.72    introduced(avatar_definition,[new_symbols(naming,[spl11_114])])).
% 2.84/0.72  fof(f3090,plain,(
% 2.84/0.72    spl11_87 <=> sP1(sK5,sK6)),
% 2.84/0.72    introduced(avatar_definition,[new_symbols(naming,[spl11_87])])).
% 2.84/0.72  fof(f3094,plain,(
% 2.84/0.72    k1_xboole_0 = sK6 | ~spl11_87),
% 2.84/0.72    inference(resolution,[],[f3092,f114])).
% 2.84/0.72  fof(f114,plain,(
% 2.84/0.72    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 2.84/0.72    inference(cnf_transformation,[],[f73])).
% 2.84/0.72  fof(f73,plain,(
% 2.84/0.72    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 2.84/0.72    inference(nnf_transformation,[],[f51])).
% 2.84/0.72  fof(f51,plain,(
% 2.84/0.72    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 2.84/0.72    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.84/0.72  fof(f3092,plain,(
% 2.84/0.72    sP1(sK5,sK6) | ~spl11_87),
% 2.84/0.72    inference(avatar_component_clause,[],[f3090])).
% 2.84/0.72  fof(f5184,plain,(
% 2.84/0.72    spl11_26 | ~spl11_175),
% 2.84/0.72    inference(avatar_split_clause,[],[f5170,f5165,f593])).
% 2.84/0.72  fof(f593,plain,(
% 2.84/0.72    spl11_26 <=> v1_funct_1(k1_xboole_0)),
% 2.84/0.72    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 2.84/0.72  fof(f5165,plain,(
% 2.84/0.72    spl11_175 <=> k1_xboole_0 = sK7),
% 2.84/0.72    introduced(avatar_definition,[new_symbols(naming,[spl11_175])])).
% 2.84/0.72  fof(f5170,plain,(
% 2.84/0.72    v1_funct_1(k1_xboole_0) | ~spl11_175),
% 2.84/0.72    inference(backward_demodulation,[],[f75,f5167])).
% 2.84/0.72  fof(f5167,plain,(
% 2.84/0.72    k1_xboole_0 = sK7 | ~spl11_175),
% 2.84/0.72    inference(avatar_component_clause,[],[f5165])).
% 2.84/0.72  fof(f75,plain,(
% 2.84/0.72    v1_funct_1(sK7)),
% 2.84/0.72    inference(cnf_transformation,[],[f59])).
% 2.84/0.72  fof(f59,plain,(
% 2.84/0.72    (((k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)),
% 2.84/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f24,f58,f57,f56,f55])).
% 2.84/0.72  fof(f55,plain,(
% 2.84/0.72    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 2.84/0.72    introduced(choice_axiom,[])).
% 2.84/0.72  fof(f56,plain,(
% 2.84/0.72    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,X4),X5) != k1_funct_1(X4,k1_funct_1(sK7,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 2.84/0.72    introduced(choice_axiom,[])).
% 2.84/0.72  fof(f57,plain,(
% 2.84/0.72    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,X4),X5) != k1_funct_1(X4,k1_funct_1(sK7,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X5) != k1_funct_1(sK8,k1_funct_1(sK7,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(X5,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8))),
% 2.84/0.72    introduced(choice_axiom,[])).
% 2.84/0.72  fof(f58,plain,(
% 2.84/0.72    ? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X5) != k1_funct_1(sK8,k1_funct_1(sK7,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(X5,sK5)) => (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5))),
% 2.84/0.72    introduced(choice_axiom,[])).
% 2.84/0.72  fof(f24,plain,(
% 2.84/0.72    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.84/0.72    inference(flattening,[],[f23])).
% 2.84/0.72  fof(f23,plain,(
% 2.84/0.72    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.84/0.72    inference(ennf_transformation,[],[f22])).
% 2.84/0.72  fof(f22,negated_conjecture,(
% 2.84/0.72    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.84/0.72    inference(negated_conjecture,[],[f21])).
% 2.84/0.72  fof(f21,conjecture,(
% 2.84/0.72    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.84/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 2.84/0.72  fof(f5169,plain,(
% 2.84/0.72    spl11_175 | ~spl11_114),
% 2.84/0.72    inference(avatar_split_clause,[],[f5161,f4148,f5165])).
% 2.84/0.72  fof(f5161,plain,(
% 2.84/0.72    k1_xboole_0 = sK7 | ~spl11_114),
% 2.84/0.72    inference(subsumption_resolution,[],[f5160,f82])).
% 2.84/0.72  fof(f82,plain,(
% 2.84/0.72    k1_xboole_0 != sK5),
% 2.84/0.72    inference(cnf_transformation,[],[f59])).
% 2.84/0.72  fof(f5160,plain,(
% 2.84/0.72    k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~spl11_114),
% 2.84/0.72    inference(subsumption_resolution,[],[f5157,f4166])).
% 2.84/0.72  fof(f4166,plain,(
% 2.84/0.72    v1_funct_2(sK7,sK5,k1_xboole_0) | ~spl11_114),
% 2.84/0.72    inference(backward_demodulation,[],[f76,f4150])).
% 2.84/0.72  fof(f4150,plain,(
% 2.84/0.72    k1_xboole_0 = sK6 | ~spl11_114),
% 2.84/0.72    inference(avatar_component_clause,[],[f4148])).
% 2.84/0.72  fof(f76,plain,(
% 2.84/0.72    v1_funct_2(sK7,sK5,sK6)),
% 2.84/0.72    inference(cnf_transformation,[],[f59])).
% 2.84/0.72  fof(f5157,plain,(
% 2.84/0.72    ~v1_funct_2(sK7,sK5,k1_xboole_0) | k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~spl11_114),
% 2.84/0.72    inference(resolution,[],[f4187,f128])).
% 2.84/0.72  fof(f128,plain,(
% 2.84/0.72    ( ! [X2,X0] : (~sP3(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 2.84/0.72    inference(equality_resolution,[],[f110])).
% 2.84/0.72  fof(f110,plain,(
% 2.84/0.72    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2)) )),
% 2.84/0.72    inference(cnf_transformation,[],[f70])).
% 2.84/0.72  fof(f70,plain,(
% 2.84/0.72    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2))),
% 2.84/0.72    inference(rectify,[],[f69])).
% 2.84/0.72  fof(f69,plain,(
% 2.84/0.72    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 2.84/0.72    inference(nnf_transformation,[],[f53])).
% 2.84/0.72  fof(f53,plain,(
% 2.84/0.72    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 2.84/0.72    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.84/0.72  fof(f4187,plain,(
% 2.84/0.72    sP3(sK7,k1_xboole_0,sK5) | ~spl11_114),
% 2.84/0.72    inference(backward_demodulation,[],[f330,f4150])).
% 2.84/0.73  fof(f330,plain,(
% 2.84/0.73    sP3(sK7,sK6,sK5)),
% 2.84/0.73    inference(resolution,[],[f117,f77])).
% 2.84/0.73  fof(f77,plain,(
% 2.84/0.73    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 2.84/0.73    inference(cnf_transformation,[],[f59])).
% 2.84/0.73  fof(f117,plain,(
% 2.84/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X2,X1,X0)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f54])).
% 2.84/0.73  fof(f54,plain,(
% 2.84/0.73    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.73    inference(definition_folding,[],[f40,f53,f52,f51])).
% 2.84/0.73  fof(f52,plain,(
% 2.84/0.73    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 2.84/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.84/0.73  fof(f40,plain,(
% 2.84/0.73    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.73    inference(flattening,[],[f39])).
% 2.84/0.73  fof(f39,plain,(
% 2.84/0.73    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.73    inference(ennf_transformation,[],[f18])).
% 2.84/0.73  fof(f18,axiom,(
% 2.84/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.84/0.73  fof(f4239,plain,(
% 2.84/0.73    ~spl11_2 | ~spl11_114),
% 2.84/0.73    inference(avatar_split_clause,[],[f4165,f4148,f162])).
% 2.84/0.73  fof(f162,plain,(
% 2.84/0.73    spl11_2 <=> v1_xboole_0(k1_xboole_0)),
% 2.84/0.73    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 2.84/0.73  fof(f4165,plain,(
% 2.84/0.73    ~v1_xboole_0(k1_xboole_0) | ~spl11_114),
% 2.84/0.73    inference(backward_demodulation,[],[f74,f4150])).
% 2.84/0.73  fof(f74,plain,(
% 2.84/0.73    ~v1_xboole_0(sK6)),
% 2.84/0.73    inference(cnf_transformation,[],[f59])).
% 2.84/0.73  fof(f4164,plain,(
% 2.84/0.73    ~spl11_7 | spl11_87 | spl11_115),
% 2.84/0.73    inference(avatar_contradiction_clause,[],[f4163])).
% 2.84/0.73  fof(f4163,plain,(
% 2.84/0.73    $false | (~spl11_7 | spl11_87 | spl11_115)),
% 2.84/0.73    inference(subsumption_resolution,[],[f4162,f198])).
% 2.84/0.73  fof(f198,plain,(
% 2.84/0.73    r2_hidden(sK9,sK5) | ~spl11_7),
% 2.84/0.73    inference(avatar_component_clause,[],[f196])).
% 2.84/0.73  fof(f196,plain,(
% 2.84/0.73    spl11_7 <=> r2_hidden(sK9,sK5)),
% 2.84/0.73    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 2.84/0.73  fof(f4162,plain,(
% 2.84/0.73    ~r2_hidden(sK9,sK5) | (spl11_87 | spl11_115)),
% 2.84/0.73    inference(forward_demodulation,[],[f4161,f3187])).
% 2.84/0.73  fof(f3187,plain,(
% 2.84/0.73    sK5 = k1_relat_1(sK7) | spl11_87),
% 2.84/0.73    inference(subsumption_resolution,[],[f3186,f3091])).
% 2.84/0.73  fof(f3091,plain,(
% 2.84/0.73    ~sP1(sK5,sK6) | spl11_87),
% 2.84/0.73    inference(avatar_component_clause,[],[f3090])).
% 2.84/0.73  fof(f3186,plain,(
% 2.84/0.73    sP1(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 2.84/0.73    inference(subsumption_resolution,[],[f3180,f76])).
% 2.84/0.73  fof(f3180,plain,(
% 2.84/0.73    ~v1_funct_2(sK7,sK5,sK6) | sP1(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 2.84/0.73    inference(resolution,[],[f77,f659])).
% 2.84/0.73  fof(f659,plain,(
% 2.84/0.73    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 2.84/0.73    inference(subsumption_resolution,[],[f654,f116])).
% 2.84/0.73  fof(f116,plain,(
% 2.84/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f54])).
% 2.84/0.73  fof(f654,plain,(
% 2.84/0.73    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.84/0.73    inference(superposition,[],[f112,f107])).
% 2.84/0.73  fof(f107,plain,(
% 2.84/0.73    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/0.73    inference(cnf_transformation,[],[f37])).
% 2.84/0.73  fof(f37,plain,(
% 2.84/0.73    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.73    inference(ennf_transformation,[],[f14])).
% 2.84/0.73  fof(f14,axiom,(
% 2.84/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.84/0.73  fof(f112,plain,(
% 2.84/0.73    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f72])).
% 2.84/0.73  fof(f72,plain,(
% 2.84/0.73    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 2.84/0.73    inference(rectify,[],[f71])).
% 2.84/0.73  fof(f71,plain,(
% 2.84/0.73    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 2.84/0.73    inference(nnf_transformation,[],[f52])).
% 2.84/0.73  fof(f4161,plain,(
% 2.84/0.73    ~r2_hidden(sK9,k1_relat_1(sK7)) | spl11_115),
% 2.84/0.73    inference(subsumption_resolution,[],[f4160,f212])).
% 2.84/0.73  fof(f212,plain,(
% 2.84/0.73    v1_relat_1(sK7)),
% 2.84/0.73    inference(resolution,[],[f106,f77])).
% 2.84/0.73  fof(f106,plain,(
% 2.84/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f36])).
% 2.84/0.73  fof(f36,plain,(
% 2.84/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.73    inference(ennf_transformation,[],[f12])).
% 2.84/0.73  fof(f12,axiom,(
% 2.84/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.84/0.73  fof(f4160,plain,(
% 2.84/0.73    ~r2_hidden(sK9,k1_relat_1(sK7)) | ~v1_relat_1(sK7) | spl11_115),
% 2.84/0.73    inference(subsumption_resolution,[],[f4159,f75])).
% 2.84/0.73  fof(f4159,plain,(
% 2.84/0.73    ~r2_hidden(sK9,k1_relat_1(sK7)) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl11_115),
% 2.84/0.73    inference(subsumption_resolution,[],[f4158,f213])).
% 2.84/0.73  fof(f213,plain,(
% 2.84/0.73    v1_relat_1(sK8)),
% 2.84/0.73    inference(resolution,[],[f106,f79])).
% 2.84/0.73  fof(f79,plain,(
% 2.84/0.73    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 2.84/0.73    inference(cnf_transformation,[],[f59])).
% 2.84/0.73  fof(f4158,plain,(
% 2.84/0.73    ~r2_hidden(sK9,k1_relat_1(sK7)) | ~v1_relat_1(sK8) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl11_115),
% 2.84/0.73    inference(subsumption_resolution,[],[f4157,f78])).
% 2.84/0.73  fof(f78,plain,(
% 2.84/0.73    v1_funct_1(sK8)),
% 2.84/0.73    inference(cnf_transformation,[],[f59])).
% 2.84/0.73  fof(f4157,plain,(
% 2.84/0.73    ~r2_hidden(sK9,k1_relat_1(sK7)) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl11_115),
% 2.84/0.73    inference(trivial_inequality_removal,[],[f4156])).
% 2.84/0.73  fof(f4156,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r2_hidden(sK9,k1_relat_1(sK7)) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl11_115),
% 2.84/0.73    inference(superposition,[],[f4154,f93])).
% 2.84/0.73  fof(f93,plain,(
% 2.84/0.73    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f33])).
% 2.84/0.73  fof(f33,plain,(
% 2.84/0.73    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.84/0.73    inference(flattening,[],[f32])).
% 2.84/0.73  fof(f32,plain,(
% 2.84/0.73    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.84/0.73    inference(ennf_transformation,[],[f11])).
% 2.84/0.73  fof(f11,axiom,(
% 2.84/0.73    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 2.84/0.73  fof(f4154,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) | spl11_115),
% 2.84/0.73    inference(avatar_component_clause,[],[f4152])).
% 2.84/0.73  fof(f4152,plain,(
% 2.84/0.73    spl11_115 <=> k1_funct_1(sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(k5_relat_1(sK7,sK8),sK9)),
% 2.84/0.73    introduced(avatar_definition,[new_symbols(naming,[spl11_115])])).
% 2.84/0.73  fof(f4155,plain,(
% 2.84/0.73    spl11_114 | ~spl11_115),
% 2.84/0.73    inference(avatar_split_clause,[],[f4146,f4152,f4148])).
% 2.84/0.73  fof(f4146,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) | k1_xboole_0 = sK6),
% 2.84/0.73    inference(subsumption_resolution,[],[f4145,f76])).
% 2.84/0.73  fof(f4145,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) | k1_xboole_0 = sK6 | ~v1_funct_2(sK7,sK5,sK6)),
% 2.84/0.73    inference(subsumption_resolution,[],[f4144,f81])).
% 2.84/0.73  fof(f81,plain,(
% 2.84/0.73    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))),
% 2.84/0.73    inference(cnf_transformation,[],[f59])).
% 2.84/0.73  fof(f4144,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) | k1_xboole_0 = sK6 | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~v1_funct_2(sK7,sK5,sK6)),
% 2.84/0.73    inference(subsumption_resolution,[],[f4143,f75])).
% 2.84/0.73  fof(f4143,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) | ~v1_funct_1(sK7) | k1_xboole_0 = sK6 | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~v1_funct_2(sK7,sK5,sK6)),
% 2.84/0.73    inference(subsumption_resolution,[],[f4142,f77])).
% 2.84/0.73  fof(f4142,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK7) | k1_xboole_0 = sK6 | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~v1_funct_2(sK7,sK5,sK6)),
% 2.84/0.73    inference(subsumption_resolution,[],[f4141,f78])).
% 2.84/0.73  fof(f4141,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK7) | k1_xboole_0 = sK6 | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~v1_funct_2(sK7,sK5,sK6)),
% 2.84/0.73    inference(subsumption_resolution,[],[f4140,f79])).
% 2.84/0.73  fof(f4140,plain,(
% 2.84/0.73    k1_funct_1(sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(k5_relat_1(sK7,sK8),sK9) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK7) | k1_xboole_0 = sK6 | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~v1_funct_2(sK7,sK5,sK6)),
% 2.84/0.73    inference(superposition,[],[f83,f847])).
% 2.84/0.73  fof(f847,plain,(
% 2.84/0.73    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k5_relat_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~v1_funct_2(X3,X0,X1)) )),
% 2.84/0.73    inference(duplicate_literal_removal,[],[f846])).
% 2.84/0.73  fof(f846,plain,(
% 2.84/0.73    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k5_relat_1(X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.84/0.73    inference(superposition,[],[f122,f121])).
% 2.84/0.73  fof(f121,plain,(
% 2.84/0.73    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f46])).
% 2.84/0.73  fof(f46,plain,(
% 2.84/0.73    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.84/0.73    inference(flattening,[],[f45])).
% 2.84/0.73  fof(f45,plain,(
% 2.84/0.73    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.84/0.73    inference(ennf_transformation,[],[f17])).
% 2.84/0.73  fof(f17,axiom,(
% 2.84/0.73    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).
% 2.84/0.73  fof(f122,plain,(
% 2.84/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f48])).
% 2.84/0.73  fof(f48,plain,(
% 2.84/0.73    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.84/0.73    inference(flattening,[],[f47])).
% 2.84/0.73  fof(f47,plain,(
% 2.84/0.73    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.84/0.73    inference(ennf_transformation,[],[f19])).
% 2.84/0.73  fof(f19,axiom,(
% 2.84/0.73    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.84/0.73  fof(f83,plain,(
% 2.84/0.73    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))),
% 2.84/0.73    inference(cnf_transformation,[],[f59])).
% 2.84/0.73  fof(f3297,plain,(
% 2.84/0.73    ~spl11_8 | spl11_87 | spl11_90),
% 2.84/0.73    inference(avatar_split_clause,[],[f3294,f3247,f3090,f200])).
% 2.84/0.73  fof(f200,plain,(
% 2.84/0.73    spl11_8 <=> v1_xboole_0(sK5)),
% 2.84/0.73    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 2.84/0.73  fof(f3247,plain,(
% 2.84/0.73    spl11_90 <=> v4_relat_1(sK7,k1_xboole_0)),
% 2.84/0.73    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).
% 2.84/0.73  fof(f3294,plain,(
% 2.84/0.73    ~v1_xboole_0(sK5) | (spl11_87 | spl11_90)),
% 2.84/0.73    inference(forward_demodulation,[],[f3293,f3187])).
% 2.84/0.73  fof(f3293,plain,(
% 2.84/0.73    ~v1_xboole_0(k1_relat_1(sK7)) | spl11_90),
% 2.84/0.73    inference(subsumption_resolution,[],[f3287,f212])).
% 2.84/0.73  fof(f3287,plain,(
% 2.84/0.73    ~v1_relat_1(sK7) | ~v1_xboole_0(k1_relat_1(sK7)) | spl11_90),
% 2.84/0.73    inference(resolution,[],[f3249,f239])).
% 2.84/0.73  fof(f239,plain,(
% 2.84/0.73    ( ! [X4,X3] : (v4_relat_1(X3,X4) | ~v1_relat_1(X3) | ~v1_xboole_0(k1_relat_1(X3))) )),
% 2.84/0.73    inference(resolution,[],[f91,f141])).
% 2.84/0.73  fof(f141,plain,(
% 2.84/0.73    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.84/0.73    inference(resolution,[],[f104,f131])).
% 2.84/0.73  fof(f131,plain,(
% 2.84/0.73    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 2.84/0.73    inference(superposition,[],[f85,f86])).
% 2.84/0.73  fof(f86,plain,(
% 2.84/0.73    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f25])).
% 2.84/0.73  fof(f25,plain,(
% 2.84/0.73    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.84/0.73    inference(ennf_transformation,[],[f1])).
% 2.84/0.73  fof(f1,axiom,(
% 2.84/0.73    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.84/0.73  fof(f85,plain,(
% 2.84/0.73    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.84/0.73    inference(cnf_transformation,[],[f5])).
% 2.84/0.73  fof(f5,axiom,(
% 2.84/0.73    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.84/0.73  fof(f104,plain,(
% 2.84/0.73    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f68])).
% 2.84/0.73  fof(f68,plain,(
% 2.84/0.73    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.84/0.73    inference(nnf_transformation,[],[f8])).
% 2.84/0.73  fof(f8,axiom,(
% 2.84/0.73    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.84/0.73  fof(f91,plain,(
% 2.84/0.73    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.84/0.73    inference(cnf_transformation,[],[f60])).
% 2.84/0.73  fof(f60,plain,(
% 2.84/0.73    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.84/0.73    inference(nnf_transformation,[],[f29])).
% 2.84/0.73  fof(f29,plain,(
% 2.84/0.73    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.84/0.73    inference(ennf_transformation,[],[f10])).
% 2.84/0.73  fof(f10,axiom,(
% 2.84/0.73    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.84/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.84/0.73  fof(f3249,plain,(
% 2.84/0.73    ~v4_relat_1(sK7,k1_xboole_0) | spl11_90),
% 2.84/0.73    inference(avatar_component_clause,[],[f3247])).
% 2.84/0.73  fof(f3286,plain,(
% 2.84/0.73    ~spl11_90 | spl11_87),
% 2.84/0.73    inference(avatar_split_clause,[],[f3244,f3090,f3247])).
% 2.84/0.74  fof(f3244,plain,(
% 2.84/0.74    ~v4_relat_1(sK7,k1_xboole_0) | spl11_87),
% 2.84/0.74    inference(subsumption_resolution,[],[f3243,f212])).
% 2.84/0.74  fof(f3243,plain,(
% 2.84/0.74    ~v4_relat_1(sK7,k1_xboole_0) | ~v1_relat_1(sK7) | spl11_87),
% 2.84/0.74    inference(subsumption_resolution,[],[f3210,f82])).
% 2.84/0.74  fof(f3210,plain,(
% 2.84/0.74    k1_xboole_0 = sK5 | ~v4_relat_1(sK7,k1_xboole_0) | ~v1_relat_1(sK7) | spl11_87),
% 2.84/0.74    inference(superposition,[],[f289,f3187])).
% 2.84/0.74  fof(f289,plain,(
% 2.84/0.74    ( ! [X1] : (k1_xboole_0 = k1_relat_1(X1) | ~v4_relat_1(X1,k1_xboole_0) | ~v1_relat_1(X1)) )),
% 2.84/0.74    inference(resolution,[],[f251,f90])).
% 2.84/0.74  fof(f90,plain,(
% 2.84/0.74    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.84/0.74    inference(cnf_transformation,[],[f60])).
% 2.84/0.74  fof(f251,plain,(
% 2.84/0.74    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 2.84/0.74    inference(resolution,[],[f97,f142])).
% 2.84/0.74  fof(f142,plain,(
% 2.84/0.74    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 2.84/0.74    inference(resolution,[],[f104,f85])).
% 2.84/0.74  fof(f97,plain,(
% 2.84/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.84/0.74    inference(cnf_transformation,[],[f62])).
% 2.84/0.74  fof(f62,plain,(
% 2.84/0.74    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.84/0.74    inference(flattening,[],[f61])).
% 2.84/0.74  fof(f61,plain,(
% 2.84/0.74    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.84/0.74    inference(nnf_transformation,[],[f2])).
% 2.84/0.74  fof(f2,axiom,(
% 2.84/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.84/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.84/0.74  fof(f2409,plain,(
% 2.84/0.74    spl11_7 | spl11_8),
% 2.84/0.74    inference(avatar_split_clause,[],[f409,f200,f196])).
% 2.84/0.74  fof(f409,plain,(
% 2.84/0.74    v1_xboole_0(sK5) | r2_hidden(sK9,sK5)),
% 2.84/0.74    inference(resolution,[],[f92,f80])).
% 2.84/0.74  fof(f80,plain,(
% 2.84/0.74    m1_subset_1(sK9,sK5)),
% 2.84/0.74    inference(cnf_transformation,[],[f59])).
% 2.84/0.74  fof(f92,plain,(
% 2.84/0.74    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.84/0.74    inference(cnf_transformation,[],[f31])).
% 2.84/0.74  fof(f31,plain,(
% 2.84/0.74    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.84/0.74    inference(flattening,[],[f30])).
% 2.84/0.74  fof(f30,plain,(
% 2.84/0.74    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.84/0.74    inference(ennf_transformation,[],[f7])).
% 2.84/0.74  fof(f7,axiom,(
% 2.84/0.74    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.84/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 2.84/0.74  fof(f1469,plain,(
% 2.84/0.74    ~spl11_26 | ~spl11_27 | ~spl11_48),
% 2.84/0.74    inference(avatar_contradiction_clause,[],[f1468])).
% 2.84/0.74  fof(f1468,plain,(
% 2.84/0.74    $false | (~spl11_26 | ~spl11_27 | ~spl11_48)),
% 2.84/0.74    inference(subsumption_resolution,[],[f1329,f1258])).
% 2.84/0.74  fof(f1258,plain,(
% 2.84/0.74    ( ! [X2] : (k1_xboole_0 = X2) ) | (~spl11_26 | ~spl11_27 | ~spl11_48)),
% 2.84/0.74    inference(subsumption_resolution,[],[f1257,f956])).
% 2.84/0.74  fof(f956,plain,(
% 2.84/0.74    ( ! [X0] : (v1_partfun1(k1_xboole_0,X0) | k1_xboole_0 = X0) ) | ~spl11_48),
% 2.84/0.74    inference(avatar_component_clause,[],[f955])).
% 2.84/0.74  fof(f955,plain,(
% 2.84/0.74    spl11_48 <=> ! [X0] : (v1_partfun1(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 2.84/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).
% 2.84/0.74  fof(f1257,plain,(
% 2.84/0.74    ( ! [X2] : (~v1_partfun1(k1_xboole_0,X2) | k1_xboole_0 = X2) ) | (~spl11_26 | ~spl11_27)),
% 2.84/0.74    inference(subsumption_resolution,[],[f1256,f211])).
% 2.84/0.74  fof(f211,plain,(
% 2.84/0.74    v1_relat_1(k1_xboole_0)),
% 2.84/0.74    inference(resolution,[],[f106,f85])).
% 2.84/0.74  fof(f1256,plain,(
% 2.84/0.74    ( ! [X2] : (k1_xboole_0 = X2 | ~v1_partfun1(k1_xboole_0,X2) | ~v1_relat_1(k1_xboole_0)) ) | (~spl11_26 | ~spl11_27)),
% 2.84/0.74    inference(subsumption_resolution,[],[f1245,f308])).
% 2.84/0.74  fof(f308,plain,(
% 2.84/0.74    ( ! [X5] : (v4_relat_1(k1_xboole_0,X5)) )),
% 2.84/0.74    inference(resolution,[],[f108,f85])).
% 2.84/0.74  fof(f108,plain,(
% 2.84/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.84/0.74    inference(cnf_transformation,[],[f38])).
% 2.84/0.74  fof(f38,plain,(
% 2.84/0.74    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.74    inference(ennf_transformation,[],[f13])).
% 2.84/0.74  fof(f13,axiom,(
% 2.84/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.84/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.84/0.74  fof(f1245,plain,(
% 2.84/0.74    ( ! [X2] : (k1_xboole_0 = X2 | ~v1_partfun1(k1_xboole_0,X2) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl11_26 | ~spl11_27)),
% 2.84/0.74    inference(superposition,[],[f1238,f289])).
% 2.84/0.74  fof(f1238,plain,(
% 2.84/0.74    ( ! [X0] : (k1_relat_1(k1_xboole_0) = X0 | ~v1_partfun1(k1_xboole_0,X0)) ) | (~spl11_26 | ~spl11_27)),
% 2.84/0.74    inference(resolution,[],[f1235,f598])).
% 2.84/0.74  fof(f598,plain,(
% 2.84/0.74    ( ! [X14,X13] : (v1_funct_2(k1_xboole_0,X13,X14) | ~v1_partfun1(k1_xboole_0,X13)) ) | ~spl11_27),
% 2.84/0.74    inference(avatar_component_clause,[],[f597])).
% 2.84/0.74  fof(f597,plain,(
% 2.84/0.74    spl11_27 <=> ! [X13,X14] : (~v1_partfun1(k1_xboole_0,X13) | v1_funct_2(k1_xboole_0,X13,X14))),
% 2.84/0.74    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).
% 2.84/0.74  fof(f1235,plain,(
% 2.84/0.74    ( ! [X1] : (~v1_funct_2(k1_xboole_0,X1,X1) | k1_relat_1(k1_xboole_0) = X1) ) | ~spl11_26),
% 2.84/0.74    inference(subsumption_resolution,[],[f1232,f85])).
% 2.84/0.74  fof(f1232,plain,(
% 2.84/0.74    ( ! [X1] : (k1_relat_1(k1_xboole_0) = X1 | ~v1_funct_2(k1_xboole_0,X1,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))) ) | ~spl11_26),
% 2.84/0.74    inference(superposition,[],[f752,f107])).
% 2.84/0.74  fof(f752,plain,(
% 2.84/0.74    ( ! [X15] : (k1_relset_1(X15,X15,k1_xboole_0) = X15 | ~v1_funct_2(k1_xboole_0,X15,X15)) ) | ~spl11_26),
% 2.84/0.74    inference(subsumption_resolution,[],[f749,f594])).
% 2.84/0.74  fof(f594,plain,(
% 2.84/0.74    v1_funct_1(k1_xboole_0) | ~spl11_26),
% 2.84/0.74    inference(avatar_component_clause,[],[f593])).
% 2.84/0.74  fof(f749,plain,(
% 2.84/0.74    ( ! [X15] : (k1_relset_1(X15,X15,k1_xboole_0) = X15 | ~v1_funct_2(k1_xboole_0,X15,X15) | ~v1_funct_1(k1_xboole_0)) )),
% 2.84/0.74    inference(resolution,[],[f94,f85])).
% 2.84/0.74  fof(f94,plain,(
% 2.84/0.74    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.84/0.74    inference(cnf_transformation,[],[f35])).
% 2.84/0.74  fof(f35,plain,(
% 2.84/0.74    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.84/0.74    inference(flattening,[],[f34])).
% 2.84/0.74  fof(f34,plain,(
% 2.84/0.74    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.84/0.74    inference(ennf_transformation,[],[f20])).
% 2.84/0.74  fof(f20,axiom,(
% 2.84/0.74    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.84/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 2.84/0.74  fof(f1329,plain,(
% 2.84/0.74    k1_xboole_0 != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | (~spl11_26 | ~spl11_27 | ~spl11_48)),
% 2.84/0.74    inference(backward_demodulation,[],[f83,f1258])).
% 2.84/0.74  fof(f957,plain,(
% 2.84/0.74    spl11_2 | spl11_48 | ~spl11_26),
% 2.84/0.74    inference(avatar_split_clause,[],[f912,f593,f955,f162])).
% 2.84/0.74  fof(f912,plain,(
% 2.84/0.74    ( ! [X0] : (v1_partfun1(k1_xboole_0,X0) | v1_xboole_0(k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl11_26),
% 2.84/0.74    inference(resolution,[],[f626,f363])).
% 2.84/0.74  fof(f363,plain,(
% 2.84/0.74    ( ! [X2] : (v1_funct_2(k1_xboole_0,X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 2.84/0.74    inference(subsumption_resolution,[],[f127,f329])).
% 2.84/0.74  fof(f329,plain,(
% 2.84/0.74    ( ! [X6,X7] : (sP3(k1_xboole_0,X6,X7)) )),
% 2.84/0.74    inference(resolution,[],[f117,f85])).
% 2.84/0.74  fof(f127,plain,(
% 2.84/0.74    ( ! [X2] : (v1_funct_2(k1_xboole_0,X2,k1_xboole_0) | k1_xboole_0 = X2 | ~sP3(k1_xboole_0,k1_xboole_0,X2)) )),
% 2.84/0.74    inference(equality_resolution,[],[f126])).
% 2.84/0.74  fof(f126,plain,(
% 2.84/0.74    ( ! [X2,X1] : (v1_funct_2(k1_xboole_0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(k1_xboole_0,X1,X2)) )),
% 2.84/0.74    inference(equality_resolution,[],[f111])).
% 2.84/0.74  fof(f111,plain,(
% 2.84/0.74    ( ! [X2,X0,X1] : (v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0 | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2)) )),
% 2.84/0.74    inference(cnf_transformation,[],[f70])).
% 2.84/0.74  fof(f626,plain,(
% 2.84/0.74    ( ! [X14,X13] : (~v1_funct_2(k1_xboole_0,X13,X14) | v1_partfun1(k1_xboole_0,X13) | v1_xboole_0(X14)) ) | ~spl11_26),
% 2.84/0.74    inference(subsumption_resolution,[],[f621,f594])).
% 2.84/0.74  fof(f621,plain,(
% 2.84/0.74    ( ! [X14,X13] : (~v1_funct_2(k1_xboole_0,X13,X14) | ~v1_funct_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,X13) | v1_xboole_0(X14)) )),
% 2.84/0.74    inference(resolution,[],[f89,f85])).
% 2.84/0.74  fof(f89,plain,(
% 2.84/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 2.84/0.74    inference(cnf_transformation,[],[f28])).
% 2.84/0.74  fof(f28,plain,(
% 2.84/0.74    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.84/0.74    inference(flattening,[],[f27])).
% 2.84/0.74  fof(f27,plain,(
% 2.84/0.74    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.84/0.74    inference(ennf_transformation,[],[f16])).
% 2.84/0.74  fof(f16,axiom,(
% 2.84/0.74    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.84/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.84/0.74  fof(f599,plain,(
% 2.84/0.74    ~spl11_26 | spl11_27),
% 2.84/0.74    inference(avatar_split_clause,[],[f588,f597,f593])).
% 2.84/0.74  fof(f588,plain,(
% 2.84/0.74    ( ! [X14,X13] : (~v1_partfun1(k1_xboole_0,X13) | ~v1_funct_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,X13,X14)) )),
% 2.84/0.74    inference(resolution,[],[f119,f85])).
% 2.84/0.74  fof(f119,plain,(
% 2.84/0.74    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 2.84/0.74    inference(cnf_transformation,[],[f42])).
% 2.84/0.74  fof(f42,plain,(
% 2.84/0.74    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.74    inference(flattening,[],[f41])).
% 2.84/0.74  fof(f41,plain,(
% 2.84/0.74    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.74    inference(ennf_transformation,[],[f15])).
% 2.84/0.74  fof(f15,axiom,(
% 2.84/0.74    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.84/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 2.84/0.74  % SZS output end Proof for theBenchmark
% 2.84/0.74  % (28795)------------------------------
% 2.84/0.74  % (28795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.84/0.74  % (28795)Termination reason: Refutation
% 2.84/0.74  
% 2.84/0.74  % (28795)Memory used [KB]: 8187
% 2.84/0.74  % (28795)Time elapsed: 0.308 s
% 2.84/0.74  % (28795)------------------------------
% 2.84/0.74  % (28795)------------------------------
% 2.84/0.74  % (28788)Success in time 0.377 s
%------------------------------------------------------------------------------
