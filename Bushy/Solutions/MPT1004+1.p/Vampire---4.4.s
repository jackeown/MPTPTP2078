%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t53_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:47 EDT 2019

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 319 expanded)
%              Number of leaves         :   36 ( 126 expanded)
%              Depth                    :   10
%              Number of atoms          :  504 (1042 expanded)
%              Number of equality atoms :   81 ( 185 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4981,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f118,f122,f133,f137,f141,f195,f199,f205,f209,f248,f272,f449,f692,f788,f796,f1112,f1470,f4074,f4265,f4267,f4514,f4979,f4980])).

fof(f4980,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) != k5_relat_1(sK4,sK5)
    | r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3)))
    | ~ r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) ),
    introduced(theory_axiom,[])).

fof(f4979,plain,
    ( ~ spl7_16
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_44
    | spl7_137
    | ~ spl7_224 ),
    inference(avatar_contradiction_clause,[],[f4978])).

fof(f4978,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_44
    | ~ spl7_137
    | ~ spl7_224 ),
    inference(subsumption_resolution,[],[f4071,f4977])).

fof(f4977,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK4,X0),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,X0)))
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f4976,f204])).

fof(f204,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl7_20
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f4976,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK4)
        | r1_tarski(k10_relat_1(sK4,X0),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,X0))) )
    | ~ spl7_16
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(resolution,[],[f4518,f271])).

fof(f271,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl7_44
  <=> r1_tarski(k2_relat_1(sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f4518,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X0),sK1)
        | ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,sK5),k9_relat_1(sK5,X1))) )
    | ~ spl7_16
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f4517,f194])).

fof(f194,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_16
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f4517,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X0),sK1)
        | ~ v1_relat_1(sK5)
        | ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,sK5),k9_relat_1(sK5,X1))) )
    | ~ spl7_24 ),
    inference(superposition,[],[f77,f214])).

fof(f214,plain,
    ( k1_relat_1(sK5) = sK1
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_24
  <=> k1_relat_1(sK5) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t160_funct_1)).

fof(f4071,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | ~ spl7_137
    | ~ spl7_224 ),
    inference(superposition,[],[f809,f1683])).

fof(f1683,plain,
    ( ! [X11] : k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),X11) = k10_relat_1(k5_relat_1(sK4,sK5),X11)
    | ~ spl7_224 ),
    inference(resolution,[],[f1111,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k8_relset_1)).

fof(f1111,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_224 ),
    inference(avatar_component_clause,[],[f1110])).

fof(f1110,plain,
    ( spl7_224
  <=> m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).

fof(f809,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | ~ spl7_137 ),
    inference(avatar_component_clause,[],[f808])).

fof(f808,plain,
    ( spl7_137
  <=> ~ r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_137])])).

fof(f4514,plain,
    ( spl7_24
    | ~ spl7_4
    | spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f165,f135,f131,f120,f213])).

fof(f120,plain,
    ( spl7_4
  <=> v1_funct_2(sK5,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f131,plain,
    ( spl7_11
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f135,plain,
    ( spl7_12
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f165,plain,
    ( k1_relat_1(sK5) = sK1
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f151,f164])).

fof(f164,plain,
    ( k1_relset_1(sK1,sK2,sK5) = sK1
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f163,f121])).

fof(f121,plain,
    ( v1_funct_2(sK5,sK1,sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f163,plain,
    ( k1_relset_1(sK1,sK2,sK5) = sK1
    | ~ v1_funct_2(sK5,sK1,sK2)
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f150,f132])).

fof(f132,plain,
    ( k1_xboole_0 != sK2
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,sK5) = sK1
    | ~ v1_funct_2(sK5,sK1,sK2)
    | ~ spl7_12 ),
    inference(resolution,[],[f136,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',d1_funct_2)).

fof(f136,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f135])).

fof(f151,plain,
    ( k1_relset_1(sK1,sK2,sK5) = k1_relat_1(sK5)
    | ~ spl7_12 ),
    inference(resolution,[],[f136,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k1_relset_1)).

fof(f4267,plain,
    ( spl7_48
    | ~ spl7_90
    | ~ spl7_124
    | ~ spl7_702 ),
    inference(avatar_split_clause,[],[f4266,f4263,f690,f447,f284])).

fof(f284,plain,
    ( spl7_48
  <=> k1_xboole_0 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f447,plain,
    ( spl7_90
  <=> v1_funct_2(sK5,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f690,plain,
    ( spl7_124
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f4263,plain,
    ( spl7_702
  <=> k1_relset_1(k1_xboole_0,sK2,sK5) = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_702])])).

fof(f4266,plain,
    ( k1_xboole_0 = k1_relat_1(sK5)
    | ~ spl7_90
    | ~ spl7_124
    | ~ spl7_702 ),
    inference(forward_demodulation,[],[f4264,f4126])).

fof(f4126,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK5)
    | ~ spl7_90
    | ~ spl7_124 ),
    inference(subsumption_resolution,[],[f742,f448])).

fof(f448,plain,
    ( v1_funct_2(sK5,k1_xboole_0,sK2)
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f447])).

fof(f742,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK5)
    | ~ v1_funct_2(sK5,k1_xboole_0,sK2)
    | ~ spl7_124 ),
    inference(resolution,[],[f691,f106])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f691,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f690])).

fof(f4264,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK5) = k1_relat_1(sK5)
    | ~ spl7_702 ),
    inference(avatar_component_clause,[],[f4263])).

fof(f4265,plain,
    ( spl7_702
    | ~ spl7_8
    | ~ spl7_132 ),
    inference(avatar_split_clause,[],[f4123,f794,f128,f4263])).

fof(f128,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f794,plain,
    ( spl7_132
  <=> k1_relset_1(sK1,sK2,sK5) = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f4123,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK5) = k1_relat_1(sK5)
    | ~ spl7_8
    | ~ spl7_132 ),
    inference(forward_demodulation,[],[f795,f129])).

fof(f129,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f795,plain,
    ( k1_relset_1(sK1,sK2,sK5) = k1_relat_1(sK5)
    | ~ spl7_132 ),
    inference(avatar_component_clause,[],[f794])).

fof(f4074,plain,
    ( ~ spl7_16
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_128
    | spl7_137
    | ~ spl7_224 ),
    inference(avatar_contradiction_clause,[],[f4073])).

fof(f4073,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_128
    | ~ spl7_137
    | ~ spl7_224 ),
    inference(subsumption_resolution,[],[f4071,f1975])).

fof(f1975,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK4,X0),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,X0)))
    | ~ spl7_16
    | ~ spl7_20
    | ~ spl7_48
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f1973,f204])).

fof(f1973,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK4)
        | r1_tarski(k10_relat_1(sK4,X0),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,X0))) )
    | ~ spl7_16
    | ~ spl7_48
    | ~ spl7_128 ),
    inference(resolution,[],[f669,f787])).

fof(f787,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | ~ spl7_128 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl7_128
  <=> r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f669,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,sK5),k9_relat_1(sK5,X1))) )
    | ~ spl7_16
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f668,f194])).

fof(f668,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
        | ~ v1_relat_1(sK5)
        | ~ v1_relat_1(X0)
        | r1_tarski(k10_relat_1(X0,X1),k10_relat_1(k5_relat_1(X0,sK5),k9_relat_1(sK5,X1))) )
    | ~ spl7_48 ),
    inference(superposition,[],[f77,f285])).

fof(f285,plain,
    ( k1_xboole_0 = k1_relat_1(sK5)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f284])).

fof(f1470,plain,
    ( spl7_276
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f543,f139,f135,f116,f112,f1468])).

fof(f1468,plain,
    ( spl7_276
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_276])])).

fof(f112,plain,
    ( spl7_0
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f116,plain,
    ( spl7_2
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f139,plain,
    ( spl7_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f543,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f540,f113])).

fof(f113,plain,
    ( v1_funct_1(sK5)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f112])).

fof(f540,plain,
    ( ~ v1_funct_1(sK5)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(resolution,[],[f187,f136])).

fof(f187,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X8)
        | k1_partfun1(sK0,sK1,X9,X10,sK4,X8) = k5_relat_1(sK4,X8) )
    | ~ spl7_2
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f172,f117])).

fof(f117,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f172,plain,
    ( ! [X10,X8,X9] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | k1_partfun1(sK0,sK1,X9,X10,sK4,X8) = k5_relat_1(sK4,X8) )
    | ~ spl7_14 ),
    inference(resolution,[],[f140,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k1_partfun1)).

fof(f140,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f1112,plain,
    ( spl7_224
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f565,f139,f135,f116,f112,f1110])).

fof(f565,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f564,f543])).

fof(f564,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f560,f113])).

fof(f560,plain,
    ( ~ v1_funct_1(sK5)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_2
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(resolution,[],[f186,f136])).

fof(f186,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X5)
        | m1_subset_1(k1_partfun1(sK0,sK1,X6,X7,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(sK0,X7))) )
    | ~ spl7_2
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f171,f117])).

fof(f171,plain,
    ( ! [X6,X7,X5] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | m1_subset_1(k1_partfun1(sK0,sK1,X6,X7,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(sK0,X7))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f140,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',dt_k1_partfun1)).

fof(f796,plain,
    ( spl7_132
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f151,f135,f794])).

fof(f788,plain,
    ( spl7_128
    | ~ spl7_8
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f298,f270,f128,f786])).

fof(f298,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | ~ spl7_8
    | ~ spl7_44 ),
    inference(superposition,[],[f271,f129])).

fof(f692,plain,
    ( spl7_124
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f595,f135,f128,f690])).

fof(f595,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(superposition,[],[f136,f129])).

fof(f449,plain,
    ( spl7_90
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f287,f128,f120,f447])).

fof(f287,plain,
    ( v1_funct_2(sK5,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(superposition,[],[f121,f129])).

fof(f272,plain,
    ( spl7_44
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f264,f246,f270])).

fof(f246,plain,
    ( spl7_38
  <=> m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f264,plain,
    ( r1_tarski(k2_relat_1(sK4),sK1)
    | ~ spl7_38 ),
    inference(resolution,[],[f247,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t3_subset)).

fof(f247,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( spl7_38
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f191,f139,f246])).

fof(f191,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1))
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f181,f178])).

fof(f178,plain,
    ( k2_relset_1(sK0,sK1,sK4) = k2_relat_1(sK4)
    | ~ spl7_14 ),
    inference(resolution,[],[f140,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k2_relset_1)).

fof(f181,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK4),k1_zfmisc_1(sK1))
    | ~ spl7_14 ),
    inference(resolution,[],[f140,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',dt_k2_relset_1)).

fof(f209,plain,
    ( ~ spl7_23
    | ~ spl7_12
    | ~ spl7_14
    | spl7_19 ),
    inference(avatar_split_clause,[],[f201,f197,f139,f135,f207])).

fof(f207,plain,
    ( spl7_23
  <=> ~ r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f197,plain,
    ( spl7_19
  <=> ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f201,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3)))
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f200,f173])).

fof(f173,plain,
    ( ! [X11] : k8_relset_1(sK0,sK1,sK4,X11) = k10_relat_1(sK4,X11)
    | ~ spl7_14 ),
    inference(resolution,[],[f140,f83])).

fof(f200,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3)))
    | ~ spl7_12
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f198,f142])).

fof(f142,plain,
    ( ! [X0] : k7_relset_1(sK1,sK2,sK5,X0) = k9_relat_1(sK5,X0)
    | ~ spl7_12 ),
    inference(resolution,[],[f136,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',redefinition_k7_relset_1)).

fof(f198,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f205,plain,
    ( spl7_20
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f179,f139,f203])).

fof(f179,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_14 ),
    inference(resolution,[],[f140,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',cc1_relset_1)).

fof(f199,plain,(
    ~ spl7_19 ),
    inference(avatar_split_clause,[],[f71,f197])).

fof(f71,plain,(
    ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X5,X1,X2)
          & v1_funct_1(X5) )
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X5,X1,X2)
          & v1_funct_1(X5) )
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X5,X1,X2)
              & v1_funct_1(X5) )
           => ( ( k1_xboole_0 = X2
               => k1_xboole_0 = X1 )
             => r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ! [X5] :
          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X5,X1,X2)
            & v1_funct_1(X5) )
         => ( ( k1_xboole_0 = X2
             => k1_xboole_0 = X1 )
           => r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t53_funct_2.p',t53_funct_2)).

fof(f195,plain,
    ( spl7_16
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f153,f135,f193])).

fof(f153,plain,
    ( v1_relat_1(sK5)
    | ~ spl7_12 ),
    inference(resolution,[],[f136,f97])).

fof(f141,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f74,f139])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f137,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f70,f135])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f133,plain,
    ( spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f67,f131,f128])).

fof(f67,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f122,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f69,f120])).

fof(f69,plain,(
    v1_funct_2(sK5,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f118,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f72,f116])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f114,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f68,f112])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
