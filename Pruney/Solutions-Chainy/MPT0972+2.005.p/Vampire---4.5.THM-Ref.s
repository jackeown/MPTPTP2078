%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 394 expanded)
%              Number of leaves         :   22 ( 130 expanded)
%              Depth                    :   18
%              Number of atoms          :  455 (2535 expanded)
%              Number of equality atoms :  120 ( 444 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f121,f130,f132,f191,f196,f214,f251,f342,f359])).

fof(f359,plain,
    ( ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f357,f129])).

fof(f129,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_6
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f357,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f58,f186])).

fof(f186,plain,
    ( sK2 = sK3
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl8_7
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f58,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f37,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f342,plain,
    ( ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f327,f129])).

fof(f327,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_3
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f58,f323])).

fof(f323,plain,
    ( sK2 = sK3
    | ~ spl8_3
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f322,f133])).

fof(f133,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f96,f116])).

fof(f116,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f96,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f53,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f322,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f321,f257])).

fof(f257,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f136,f195])).

fof(f195,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl8_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f136,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f56,f75])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f321,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f320,f95])).

fof(f95,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f53,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f320,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f319,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f319,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f318,f135])).

fof(f135,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f74])).

fof(f318,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f309,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f309,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(superposition,[],[f62,f298])).

fof(f298,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl8_8 ),
    inference(resolution,[],[f190,f57])).

fof(f57,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f190,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl8_8
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f251,plain,
    ( ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f249,f238])).

fof(f238,plain,
    ( k1_xboole_0 != sK3
    | ~ spl8_2
    | spl8_7 ),
    inference(backward_demodulation,[],[f185,f225])).

fof(f225,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_2 ),
    inference(resolution,[],[f220,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f220,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK2 = X0 )
    | ~ spl8_2 ),
    inference(resolution,[],[f110,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f110,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_2
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f185,plain,
    ( sK2 != sK3
    | spl8_7 ),
    inference(avatar_component_clause,[],[f184])).

fof(f249,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f227,f225])).

fof(f227,plain,
    ( sK2 = sK3
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f220,f217])).

fof(f217,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f216,f59])).

fof(f216,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3)
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f134,f120])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f134,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f56,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f214,plain,
    ( spl8_1
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f204,f59])).

fof(f204,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_1
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f106,f120])).

fof(f106,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f196,plain,
    ( spl8_9
    | spl8_4 ),
    inference(avatar_split_clause,[],[f143,f118,f193])).

fof(f143,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f138,f55])).

fof(f55,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f138,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f191,plain,
    ( spl8_7
    | spl8_8
    | ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f182,f118,f114,f188,f184])).

fof(f182,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ spl8_3
    | spl8_4 ),
    inference(subsumption_resolution,[],[f181,f135])).

fof(f181,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4 ),
    inference(subsumption_resolution,[],[f180,f54])).

fof(f180,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4 ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4 ),
    inference(superposition,[],[f159,f145])).

fof(f145,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl8_4 ),
    inference(backward_demodulation,[],[f136,f144])).

fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f143,f119])).

fof(f119,plain,
    ( k1_xboole_0 != sK1
    | spl8_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f159,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f158,f95])).

fof(f158,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f155,f51])).

fof(f155,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_3 ),
    inference(superposition,[],[f61,f133])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f132,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f125,f101])).

fof(f101,plain,(
    ~ sP7(sK1,sK0) ),
    inference(resolution,[],[f53,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP7(X1,X0) ) ),
    inference(general_splitting,[],[f84,f92_D])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f92_D])).

fof(f92_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP7(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f125,plain,
    ( sP7(sK1,sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_5
  <=> sP7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f130,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f100,f127,f123])).

fof(f100,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP7(sK1,sK0) ),
    inference(resolution,[],[f53,f92])).

fof(f121,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f112,f118,f114])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f98,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f53,f77])).

fof(f111,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f94,f108,f104])).

fof(f94,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f53,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:54:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (1205)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (1204)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (1221)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (1202)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (1213)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (1222)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (1201)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (1214)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (1218)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (1199)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (1206)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (1210)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (1217)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (1207)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (1207)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f364,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f111,f121,f130,f132,f191,f196,f214,f251,f342,f359])).
% 0.22/0.56  fof(f359,plain,(
% 0.22/0.56    ~spl8_6 | ~spl8_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f358])).
% 0.22/0.56  fof(f358,plain,(
% 0.22/0.56    $false | (~spl8_6 | ~spl8_7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f357,f129])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl8_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    spl8_6 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.56  fof(f357,plain,(
% 0.22/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl8_7),
% 0.22/0.56    inference(forward_demodulation,[],[f58,f186])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    sK2 = sK3 | ~spl8_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f184])).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    spl8_7 <=> sK2 = sK3),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f37,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.56    inference(negated_conjecture,[],[f16])).
% 0.22/0.56  fof(f16,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.22/0.56  fof(f342,plain,(
% 0.22/0.56    ~spl8_3 | ~spl8_6 | ~spl8_8 | ~spl8_9),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f341])).
% 0.22/0.56  fof(f341,plain,(
% 0.22/0.56    $false | (~spl8_3 | ~spl8_6 | ~spl8_8 | ~spl8_9)),
% 0.22/0.56    inference(subsumption_resolution,[],[f327,f129])).
% 0.22/0.56  fof(f327,plain,(
% 0.22/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl8_3 | ~spl8_8 | ~spl8_9)),
% 0.22/0.56    inference(backward_demodulation,[],[f58,f323])).
% 0.22/0.56  fof(f323,plain,(
% 0.22/0.56    sK2 = sK3 | (~spl8_3 | ~spl8_8 | ~spl8_9)),
% 0.22/0.56    inference(subsumption_resolution,[],[f322,f133])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2) | ~spl8_3),
% 0.22/0.56    inference(backward_demodulation,[],[f96,f116])).
% 0.22/0.56  fof(f116,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    spl8_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f53,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f322,plain,(
% 0.22/0.56    sK0 != k1_relat_1(sK2) | sK2 = sK3 | (~spl8_8 | ~spl8_9)),
% 0.22/0.56    inference(forward_demodulation,[],[f321,f257])).
% 0.22/0.56  fof(f257,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK3) | ~spl8_9),
% 0.22/0.56    inference(backward_demodulation,[],[f136,f195])).
% 0.22/0.56  fof(f195,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f193])).
% 0.22/0.56  fof(f193,plain,(
% 0.22/0.56    spl8_9 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f56,f75])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f321,plain,(
% 0.22/0.56    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~spl8_8),
% 0.22/0.56    inference(subsumption_resolution,[],[f320,f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    v1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f53,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.56  fof(f320,plain,(
% 0.22/0.56    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl8_8),
% 0.22/0.56    inference(subsumption_resolution,[],[f319,f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    v1_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f319,plain,(
% 0.22/0.56    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_8),
% 0.22/0.56    inference(subsumption_resolution,[],[f318,f135])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    v1_relat_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f56,f74])).
% 0.22/0.56  fof(f318,plain,(
% 0.22/0.56    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_8),
% 0.22/0.56    inference(subsumption_resolution,[],[f309,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    v1_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f309,plain,(
% 0.22/0.56    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_8),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f308])).
% 0.22/0.56  fof(f308,plain,(
% 0.22/0.56    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_8),
% 0.22/0.56    inference(superposition,[],[f62,f298])).
% 0.22/0.56  fof(f298,plain,(
% 0.22/0.56    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl8_8),
% 0.22/0.56    inference(resolution,[],[f190,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f190,plain,(
% 0.22/0.56    r2_hidden(sK4(sK2,sK3),sK0) | ~spl8_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f188])).
% 0.22/0.56  fof(f188,plain,(
% 0.22/0.56    spl8_8 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.56  fof(f251,plain,(
% 0.22/0.56    ~spl8_2 | ~spl8_4 | spl8_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f250])).
% 0.22/0.56  fof(f250,plain,(
% 0.22/0.56    $false | (~spl8_2 | ~spl8_4 | spl8_7)),
% 0.22/0.56    inference(subsumption_resolution,[],[f249,f238])).
% 0.22/0.56  fof(f238,plain,(
% 0.22/0.56    k1_xboole_0 != sK3 | (~spl8_2 | spl8_7)),
% 0.22/0.56    inference(backward_demodulation,[],[f185,f225])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | ~spl8_2),
% 0.22/0.56    inference(resolution,[],[f220,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.56  fof(f220,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | sK2 = X0) ) | ~spl8_2),
% 0.22/0.56    inference(resolution,[],[f110,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    v1_xboole_0(sK2) | ~spl8_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f108])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    spl8_2 <=> v1_xboole_0(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.56  fof(f185,plain,(
% 0.22/0.56    sK2 != sK3 | spl8_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f184])).
% 0.22/0.56  fof(f249,plain,(
% 0.22/0.56    k1_xboole_0 = sK3 | (~spl8_2 | ~spl8_4)),
% 0.22/0.56    inference(forward_demodulation,[],[f227,f225])).
% 0.22/0.56  fof(f227,plain,(
% 0.22/0.56    sK2 = sK3 | (~spl8_2 | ~spl8_4)),
% 0.22/0.56    inference(resolution,[],[f220,f217])).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    v1_xboole_0(sK3) | ~spl8_4),
% 0.22/0.56    inference(subsumption_resolution,[],[f216,f59])).
% 0.22/0.56  fof(f216,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK3) | ~spl8_4),
% 0.22/0.56    inference(forward_demodulation,[],[f134,f120])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | ~spl8_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f118])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    spl8_4 <=> k1_xboole_0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    v1_xboole_0(sK3) | ~v1_xboole_0(sK1)),
% 0.22/0.56    inference(resolution,[],[f56,f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.56  fof(f214,plain,(
% 0.22/0.56    spl8_1 | ~spl8_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f213])).
% 0.22/0.56  fof(f213,plain,(
% 0.22/0.56    $false | (spl8_1 | ~spl8_4)),
% 0.22/0.56    inference(subsumption_resolution,[],[f204,f59])).
% 0.22/0.56  fof(f204,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0) | (spl8_1 | ~spl8_4)),
% 0.22/0.56    inference(backward_demodulation,[],[f106,f120])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ~v1_xboole_0(sK1) | spl8_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f104])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    spl8_1 <=> v1_xboole_0(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.56  fof(f196,plain,(
% 0.22/0.56    spl8_9 | spl8_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f143,f118,f193])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f138,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.56    inference(resolution,[],[f56,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f191,plain,(
% 0.22/0.56    spl8_7 | spl8_8 | ~spl8_3 | spl8_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f182,f118,f114,f188,f184])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | (~spl8_3 | spl8_4)),
% 0.22/0.56    inference(subsumption_resolution,[],[f181,f135])).
% 0.22/0.56  fof(f181,plain,(
% 0.22/0.56    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4)),
% 0.22/0.56    inference(subsumption_resolution,[],[f180,f54])).
% 0.22/0.56  fof(f180,plain,(
% 0.22/0.56    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f179])).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    sK0 != sK0 | r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4)),
% 0.22/0.56    inference(superposition,[],[f159,f145])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK3) | spl8_4),
% 0.22/0.56    inference(backward_demodulation,[],[f136,f144])).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | spl8_4),
% 0.22/0.56    inference(subsumption_resolution,[],[f143,f119])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    k1_xboole_0 != sK1 | spl8_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f118])).
% 0.22/0.56  fof(f159,plain,(
% 0.22/0.56    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl8_3),
% 0.22/0.56    inference(subsumption_resolution,[],[f158,f95])).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | ~spl8_3),
% 0.22/0.56    inference(subsumption_resolution,[],[f155,f51])).
% 0.22/0.56  fof(f155,plain,(
% 0.22/0.56    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_3),
% 0.22/0.56    inference(superposition,[],[f61,f133])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f132,plain,(
% 0.22/0.56    ~spl8_5),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f131])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    $false | ~spl8_5),
% 0.22/0.56    inference(subsumption_resolution,[],[f125,f101])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ~sP7(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f53,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP7(X1,X0)) )),
% 0.22/0.56    inference(general_splitting,[],[f84,f92_D])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP7(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f92_D])).
% 0.22/0.56  fof(f92_D,plain,(
% 0.22/0.56    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP7(X1,X0)) )),
% 0.22/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    sP7(sK1,sK0) | ~spl8_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f123])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    spl8_5 <=> sP7(sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    spl8_5 | spl8_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f100,f127,f123])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK1,sK2,sK2) | sP7(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f53,f92])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    spl8_3 | spl8_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f112,f118,f114])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f98,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(resolution,[],[f53,f77])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ~spl8_1 | spl8_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f94,f108,f104])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    v1_xboole_0(sK2) | ~v1_xboole_0(sK1)),
% 0.22/0.56    inference(resolution,[],[f53,f66])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (1207)------------------------------
% 0.22/0.56  % (1207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1207)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (1207)Memory used [KB]: 10874
% 0.22/0.56  % (1207)Time elapsed: 0.136 s
% 0.22/0.56  % (1207)------------------------------
% 0.22/0.56  % (1207)------------------------------
% 0.22/0.56  % (1225)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (1226)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.56  % (1227)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.56  % (1198)Success in time 0.193 s
%------------------------------------------------------------------------------
