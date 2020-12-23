%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:09 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 253 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  361 (1154 expanded)
%              Number of equality atoms :  107 ( 242 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f120,f134,f141,f162,f166,f174,f178,f198,f215,f238,f265,f380])).

fof(f380,plain,
    ( ~ spl7_2
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl7_2
    | spl7_14 ),
    inference(unit_resulting_resolution,[],[f313,f333])).

fof(f333,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f288,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f288,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f276,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f276,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f83,f108])).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f83,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f313,plain,
    ( k1_xboole_0 != sK2
    | ~ spl7_2
    | spl7_14 ),
    inference(backward_demodulation,[],[f213,f301])).

fof(f301,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f285,f54])).

fof(f285,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f272,f59])).

fof(f272,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f74,f108])).

fof(f74,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f47])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f213,plain,
    ( sK2 != sK3
    | spl7_14 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl7_14
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f265,plain,(
    ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f33,f245,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f245,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f30,f214])).

fof(f214,plain,
    ( sK2 = sK3
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f212])).

fof(f30,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f238,plain,
    ( ~ spl7_5
    | ~ spl7_8
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_8
    | spl7_13 ),
    inference(trivial_inequality_removal,[],[f235])).

fof(f235,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK2)) != k1_funct_1(sK2,sK4(sK2,sK2))
    | ~ spl7_5
    | ~ spl7_8
    | spl7_13 ),
    inference(backward_demodulation,[],[f210,f219])).

fof(f219,plain,
    ( sK2 = sK3
    | ~ spl7_5
    | ~ spl7_8
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f81,f31,f133,f216,f161])).

fof(f161,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl7_8
  <=> ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f216,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f210,f26])).

fof(f26,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f133,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_5
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f33,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f210,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl7_13
  <=> k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f215,plain,
    ( ~ spl7_10
    | ~ spl7_13
    | spl7_14
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f202,f164,f131,f212,f208,f180])).

fof(f180,plain,
    ( spl7_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f164,plain,
    ( spl7_9
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK3 = X0
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f202,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f200,f133])).

fof(f200,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(resolution,[],[f165,f31])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK3 = X0
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f164])).

fof(f198,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f33,f182,f57])).

fof(f182,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f180])).

fof(f178,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f27,f158])).

fof(f158,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl7_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f174,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f29,f154,f57])).

fof(f154,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl7_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f166,plain,
    ( ~ spl7_6
    | spl7_9
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f122,f110,f164,f152])).

fof(f110,plain,
    ( spl7_3
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f122,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | sK3 = X0 )
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f67,f112])).

fof(f112,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
      | sK3 = X0 ) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f162,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f123,f110,f160,f156,f152])).

fof(f123,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | sK3 = X0 )
    | ~ spl7_3 ),
    inference(superposition,[],[f39,f112])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f83,f129,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f134,plain,
    ( ~ spl7_4
    | spl7_2
    | spl7_5 ),
    inference(avatar_split_clause,[],[f88,f131,f106,f127])).

fof(f88,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f70,f80])).

fof(f80,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f33,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f32,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f120,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f74,f104,f46])).

fof(f104,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f113,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f79,f110,f106,f102])).

fof(f79,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f69,f71])).

fof(f71,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f29,f56])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f28,f53])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:13:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (31550)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (31539)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (31547)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (31565)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (31541)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (31566)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.48/0.55  % (31562)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.56  % (31546)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.56  % (31542)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.48/0.56  % (31560)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.48/0.56  % (31564)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.56  % (31563)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.56  % (31542)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f381,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(avatar_sat_refutation,[],[f113,f120,f134,f141,f162,f166,f174,f178,f198,f215,f238,f265,f380])).
% 1.48/0.56  fof(f380,plain,(
% 1.48/0.56    ~spl7_2 | spl7_14),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f376])).
% 1.48/0.56  fof(f376,plain,(
% 1.48/0.56    $false | (~spl7_2 | spl7_14)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f313,f333])).
% 1.48/0.56  fof(f333,plain,(
% 1.48/0.56    k1_xboole_0 = sK2 | ~spl7_2),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f288,f54])).
% 1.48/0.56  fof(f54,plain,(
% 1.48/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.48/0.56    inference(cnf_transformation,[],[f23])).
% 1.48/0.56  fof(f23,plain,(
% 1.48/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.48/0.56    inference(ennf_transformation,[],[f4])).
% 1.48/0.56  fof(f4,axiom,(
% 1.48/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.48/0.56  fof(f288,plain,(
% 1.48/0.56    r1_tarski(sK2,k1_xboole_0) | ~spl7_2),
% 1.48/0.56    inference(forward_demodulation,[],[f276,f59])).
% 1.48/0.56  fof(f59,plain,(
% 1.48/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.48/0.56    inference(equality_resolution,[],[f38])).
% 1.48/0.56  fof(f38,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f5])).
% 1.48/0.56  fof(f5,axiom,(
% 1.48/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.48/0.56  fof(f276,plain,(
% 1.48/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl7_2),
% 1.48/0.56    inference(backward_demodulation,[],[f83,f108])).
% 1.48/0.56  fof(f108,plain,(
% 1.48/0.56    k1_xboole_0 = sK1 | ~spl7_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f106])).
% 1.48/0.56  fof(f106,plain,(
% 1.48/0.56    spl7_2 <=> k1_xboole_0 = sK1),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.48/0.56  fof(f83,plain,(
% 1.48/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f33,f47])).
% 1.48/0.56  fof(f47,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.48/0.56  fof(f33,plain,(
% 1.48/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  fof(f15,plain,(
% 1.48/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.48/0.56    inference(flattening,[],[f14])).
% 1.48/0.56  fof(f14,plain,(
% 1.48/0.56    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.48/0.56    inference(ennf_transformation,[],[f13])).
% 1.48/0.56  fof(f13,negated_conjecture,(
% 1.48/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.48/0.56    inference(negated_conjecture,[],[f12])).
% 1.48/0.56  fof(f12,conjecture,(
% 1.48/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 1.48/0.56  fof(f313,plain,(
% 1.48/0.56    k1_xboole_0 != sK2 | (~spl7_2 | spl7_14)),
% 1.48/0.56    inference(backward_demodulation,[],[f213,f301])).
% 1.48/0.56  fof(f301,plain,(
% 1.48/0.56    k1_xboole_0 = sK3 | ~spl7_2),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f285,f54])).
% 1.48/0.56  fof(f285,plain,(
% 1.48/0.56    r1_tarski(sK3,k1_xboole_0) | ~spl7_2),
% 1.48/0.56    inference(forward_demodulation,[],[f272,f59])).
% 1.48/0.56  fof(f272,plain,(
% 1.48/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl7_2),
% 1.48/0.56    inference(backward_demodulation,[],[f74,f108])).
% 1.48/0.56  fof(f74,plain,(
% 1.48/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f29,f47])).
% 1.48/0.56  fof(f29,plain,(
% 1.48/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  fof(f213,plain,(
% 1.48/0.56    sK2 != sK3 | spl7_14),
% 1.48/0.56    inference(avatar_component_clause,[],[f212])).
% 1.48/0.56  fof(f212,plain,(
% 1.48/0.56    spl7_14 <=> sK2 = sK3),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.48/0.56  fof(f265,plain,(
% 1.48/0.56    ~spl7_14),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f261])).
% 1.48/0.56  fof(f261,plain,(
% 1.48/0.56    $false | ~spl7_14),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f33,f245,f66])).
% 1.48/0.56  fof(f66,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.48/0.56    inference(duplicate_literal_removal,[],[f58])).
% 1.48/0.56  fof(f58,plain,(
% 1.48/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.48/0.56    inference(equality_resolution,[],[f34])).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f17])).
% 1.48/0.56  fof(f17,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(flattening,[],[f16])).
% 1.48/0.56  fof(f16,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.48/0.56    inference(ennf_transformation,[],[f10])).
% 1.48/0.56  fof(f10,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.48/0.56  fof(f245,plain,(
% 1.48/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_14),
% 1.48/0.56    inference(backward_demodulation,[],[f30,f214])).
% 1.48/0.56  fof(f214,plain,(
% 1.48/0.56    sK2 = sK3 | ~spl7_14),
% 1.48/0.56    inference(avatar_component_clause,[],[f212])).
% 1.48/0.56  fof(f30,plain,(
% 1.48/0.56    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  fof(f238,plain,(
% 1.48/0.56    ~spl7_5 | ~spl7_8 | spl7_13),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f237])).
% 1.48/0.56  fof(f237,plain,(
% 1.48/0.56    $false | (~spl7_5 | ~spl7_8 | spl7_13)),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f235])).
% 1.48/0.56  fof(f235,plain,(
% 1.48/0.56    k1_funct_1(sK2,sK4(sK2,sK2)) != k1_funct_1(sK2,sK4(sK2,sK2)) | (~spl7_5 | ~spl7_8 | spl7_13)),
% 1.48/0.56    inference(backward_demodulation,[],[f210,f219])).
% 1.48/0.56  fof(f219,plain,(
% 1.48/0.56    sK2 = sK3 | (~spl7_5 | ~spl7_8 | spl7_13)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f81,f31,f133,f216,f161])).
% 1.48/0.56  fof(f161,plain,(
% 1.48/0.56    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_8),
% 1.48/0.56    inference(avatar_component_clause,[],[f160])).
% 1.48/0.56  fof(f160,plain,(
% 1.48/0.56    spl7_8 <=> ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.48/0.56  fof(f216,plain,(
% 1.48/0.56    ~r2_hidden(sK4(sK3,sK2),sK0) | spl7_13),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f210,f26])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  fof(f133,plain,(
% 1.48/0.56    sK0 = k1_relat_1(sK2) | ~spl7_5),
% 1.48/0.56    inference(avatar_component_clause,[],[f131])).
% 1.48/0.56  fof(f131,plain,(
% 1.48/0.56    spl7_5 <=> sK0 = k1_relat_1(sK2)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    v1_funct_1(sK2)),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  fof(f81,plain,(
% 1.48/0.56    v1_relat_1(sK2)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f33,f57])).
% 1.48/0.56  fof(f57,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f25])).
% 1.48/0.56  fof(f25,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f8])).
% 1.48/0.56  fof(f8,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.56  fof(f210,plain,(
% 1.48/0.56    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | spl7_13),
% 1.48/0.56    inference(avatar_component_clause,[],[f208])).
% 1.48/0.56  fof(f208,plain,(
% 1.48/0.56    spl7_13 <=> k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.48/0.56  fof(f215,plain,(
% 1.48/0.56    ~spl7_10 | ~spl7_13 | spl7_14 | ~spl7_5 | ~spl7_9),
% 1.48/0.56    inference(avatar_split_clause,[],[f202,f164,f131,f212,f208,f180])).
% 1.48/0.56  fof(f180,plain,(
% 1.48/0.56    spl7_10 <=> v1_relat_1(sK2)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.48/0.56  fof(f164,plain,(
% 1.48/0.56    spl7_9 <=> ! [X0] : (k1_relat_1(X0) != sK0 | sK3 = X0 | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.48/0.56  fof(f202,plain,(
% 1.48/0.56    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK2) | (~spl7_5 | ~spl7_9)),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f201])).
% 1.48/0.56  fof(f201,plain,(
% 1.48/0.56    sK0 != sK0 | sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK2) | (~spl7_5 | ~spl7_9)),
% 1.48/0.56    inference(forward_demodulation,[],[f200,f133])).
% 1.48/0.56  fof(f200,plain,(
% 1.48/0.56    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl7_9),
% 1.48/0.56    inference(resolution,[],[f165,f31])).
% 1.48/0.56  fof(f165,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_funct_1(X0) | sK3 = X0 | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | k1_relat_1(X0) != sK0 | ~v1_relat_1(X0)) ) | ~spl7_9),
% 1.48/0.56    inference(avatar_component_clause,[],[f164])).
% 1.48/0.56  fof(f198,plain,(
% 1.48/0.56    spl7_10),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f193])).
% 1.48/0.56  fof(f193,plain,(
% 1.48/0.56    $false | spl7_10),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f33,f182,f57])).
% 1.48/0.56  fof(f182,plain,(
% 1.48/0.56    ~v1_relat_1(sK2) | spl7_10),
% 1.48/0.56    inference(avatar_component_clause,[],[f180])).
% 1.48/0.56  fof(f178,plain,(
% 1.48/0.56    spl7_7),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f175])).
% 1.48/0.56  fof(f175,plain,(
% 1.48/0.56    $false | spl7_7),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f27,f158])).
% 1.48/0.56  fof(f158,plain,(
% 1.48/0.56    ~v1_funct_1(sK3) | spl7_7),
% 1.48/0.56    inference(avatar_component_clause,[],[f156])).
% 1.48/0.56  fof(f156,plain,(
% 1.48/0.56    spl7_7 <=> v1_funct_1(sK3)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.48/0.56  fof(f27,plain,(
% 1.48/0.56    v1_funct_1(sK3)),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  fof(f174,plain,(
% 1.48/0.56    spl7_6),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f169])).
% 1.48/0.56  fof(f169,plain,(
% 1.48/0.56    $false | spl7_6),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f29,f154,f57])).
% 1.48/0.56  fof(f154,plain,(
% 1.48/0.56    ~v1_relat_1(sK3) | spl7_6),
% 1.48/0.56    inference(avatar_component_clause,[],[f152])).
% 1.48/0.56  fof(f152,plain,(
% 1.48/0.56    spl7_6 <=> v1_relat_1(sK3)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.48/0.56  fof(f166,plain,(
% 1.48/0.56    ~spl7_6 | spl7_9 | ~spl7_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f122,f110,f164,f152])).
% 1.48/0.56  fof(f110,plain,(
% 1.48/0.56    spl7_3 <=> sK0 = k1_relat_1(sK3)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.48/0.56  fof(f122,plain,(
% 1.48/0.56    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0) ) | ~spl7_3),
% 1.48/0.56    inference(backward_demodulation,[],[f67,f112])).
% 1.48/0.56  fof(f112,plain,(
% 1.48/0.56    sK0 = k1_relat_1(sK3) | ~spl7_3),
% 1.48/0.56    inference(avatar_component_clause,[],[f110])).
% 1.48/0.56  fof(f67,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0) )),
% 1.48/0.56    inference(resolution,[],[f27,f40])).
% 1.48/0.56  fof(f40,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 1.48/0.56    inference(cnf_transformation,[],[f19])).
% 1.48/0.56  fof(f19,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(flattening,[],[f18])).
% 1.48/0.56  fof(f18,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.56    inference(ennf_transformation,[],[f7])).
% 1.48/0.56  fof(f7,axiom,(
% 1.48/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.48/0.56  fof(f162,plain,(
% 1.48/0.56    ~spl7_6 | ~spl7_7 | spl7_8 | ~spl7_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f123,f110,f160,f156,f152])).
% 1.48/0.56  fof(f123,plain,(
% 1.48/0.56    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0) ) | ~spl7_3),
% 1.48/0.56    inference(superposition,[],[f39,f112])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 1.48/0.56    inference(cnf_transformation,[],[f19])).
% 1.48/0.56  fof(f141,plain,(
% 1.48/0.56    spl7_4),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f137])).
% 1.48/0.56  fof(f137,plain,(
% 1.48/0.56    $false | spl7_4),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f83,f129,f46])).
% 1.48/0.56  fof(f46,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f6])).
% 1.48/0.56  fof(f129,plain,(
% 1.48/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f127])).
% 1.48/0.56  fof(f127,plain,(
% 1.48/0.56    spl7_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.48/0.56  fof(f134,plain,(
% 1.48/0.56    ~spl7_4 | spl7_2 | spl7_5),
% 1.48/0.56    inference(avatar_split_clause,[],[f88,f131,f106,f127])).
% 1.48/0.56  fof(f88,plain,(
% 1.48/0.56    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    inference(backward_demodulation,[],[f70,f80])).
% 1.48/0.56  fof(f80,plain,(
% 1.48/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f33,f56])).
% 1.48/0.56  fof(f56,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    inference(resolution,[],[f32,f53])).
% 1.48/0.56  fof(f53,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f22])).
% 1.48/0.56  fof(f22,plain,(
% 1.48/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(flattening,[],[f21])).
% 1.48/0.56  fof(f21,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f11])).
% 1.48/0.56  fof(f11,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.48/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.48/0.56  fof(f32,plain,(
% 1.48/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  fof(f120,plain,(
% 1.48/0.56    spl7_1),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f116])).
% 1.48/0.56  fof(f116,plain,(
% 1.48/0.56    $false | spl7_1),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f74,f104,f46])).
% 1.48/0.56  fof(f104,plain,(
% 1.48/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_1),
% 1.48/0.56    inference(avatar_component_clause,[],[f102])).
% 1.48/0.56  fof(f102,plain,(
% 1.48/0.56    spl7_1 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.48/0.56  fof(f113,plain,(
% 1.48/0.56    ~spl7_1 | spl7_2 | spl7_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f79,f110,f106,f102])).
% 1.48/0.56  fof(f79,plain,(
% 1.48/0.56    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    inference(backward_demodulation,[],[f69,f71])).
% 1.48/0.56  fof(f71,plain,(
% 1.48/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f29,f56])).
% 1.48/0.56  fof(f69,plain,(
% 1.48/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    inference(resolution,[],[f28,f53])).
% 1.48/0.56  fof(f28,plain,(
% 1.48/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f15])).
% 1.48/0.56  % SZS output end Proof for theBenchmark
% 1.48/0.56  % (31542)------------------------------
% 1.48/0.56  % (31542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (31542)Termination reason: Refutation
% 1.48/0.56  
% 1.48/0.56  % (31542)Memory used [KB]: 6396
% 1.48/0.56  % (31542)Time elapsed: 0.140 s
% 1.48/0.56  % (31542)------------------------------
% 1.48/0.56  % (31542)------------------------------
% 1.48/0.56  % (31558)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.56  % (31540)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.48/0.56  % (31549)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (31544)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.57  % (31555)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.57  % (31537)Success in time 0.201 s
%------------------------------------------------------------------------------
