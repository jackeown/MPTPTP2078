%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1013+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:02 EST 2020

% Result     : Theorem 30.55s
% Output     : Refutation 30.55s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 185 expanded)
%              Number of leaves         :   22 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 ( 554 expanded)
%              Number of equality atoms :   76 ( 214 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4723,f4728,f4733,f4738,f4743,f5171,f5235,f5641,f5670,f5688,f5725,f5764,f5769,f74240])).

fof(f74240,plain,
    ( ~ spl339_30
    | ~ spl339_50
    | ~ spl339_69
    | ~ spl339_92
    | ~ spl339_97
    | spl339_98 ),
    inference(avatar_contradiction_clause,[],[f74239])).

fof(f74239,plain,
    ( $false
    | ~ spl339_30
    | ~ spl339_50
    | ~ spl339_69
    | ~ spl339_92
    | ~ spl339_97
    | spl339_98 ),
    inference(subsumption_resolution,[],[f74238,f5768])).

fof(f5768,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))
    | spl339_98 ),
    inference(avatar_component_clause,[],[f5766])).

fof(f5766,plain,
    ( spl339_98
  <=> sK0 = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_98])])).

fof(f74238,plain,
    ( sK0 = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))
    | ~ spl339_30
    | ~ spl339_50
    | ~ spl339_69
    | ~ spl339_92
    | ~ spl339_97 ),
    inference(forward_demodulation,[],[f74237,f5724])).

fof(f5724,plain,
    ( sK0 = k9_relat_1(sK1,sK0)
    | ~ spl339_92 ),
    inference(avatar_component_clause,[],[f5722])).

fof(f5722,plain,
    ( spl339_92
  <=> sK0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_92])])).

fof(f74237,plain,
    ( k9_relat_1(sK1,sK0) = k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))
    | ~ spl339_30
    | ~ spl339_50
    | ~ spl339_69
    | ~ spl339_97 ),
    inference(forward_demodulation,[],[f74236,f5234])).

fof(f5234,plain,
    ( sK0 = k9_relat_1(sK2,sK0)
    | ~ spl339_50 ),
    inference(avatar_component_clause,[],[f5232])).

fof(f5232,plain,
    ( spl339_50
  <=> sK0 = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_50])])).

fof(f74236,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,k9_relat_1(sK2,sK0))
    | ~ spl339_30
    | ~ spl339_69
    | ~ spl339_97 ),
    inference(forward_demodulation,[],[f74060,f74192])).

fof(f74192,plain,
    ( ! [X0] : k9_relat_1(sK1,k9_relat_1(sK2,X0)) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),X0)
    | ~ spl339_30
    | ~ spl339_69
    | ~ spl339_97 ),
    inference(forward_demodulation,[],[f73942,f22354])).

fof(f22354,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK2,sK1),X0) = k9_relat_1(sK1,k9_relat_1(sK2,X0))
    | ~ spl339_30
    | ~ spl339_69 ),
    inference(unit_resulting_resolution,[],[f5102,f5577,f4069])).

fof(f4069,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f2266])).

fof(f2266,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f762])).

fof(f762,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f5577,plain,
    ( v1_relat_1(sK1)
    | ~ spl339_69 ),
    inference(avatar_component_clause,[],[f5575])).

fof(f5575,plain,
    ( spl339_69
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_69])])).

fof(f5102,plain,
    ( v1_relat_1(sK2)
    | ~ spl339_30 ),
    inference(avatar_component_clause,[],[f5100])).

fof(f5100,plain,
    ( spl339_30
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_30])])).

fof(f73942,plain,
    ( ! [X0] : k9_relat_1(k5_relat_1(sK2,sK1),X0) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),X0)
    | ~ spl339_97 ),
    inference(unit_resulting_resolution,[],[f5763,f4172])).

fof(f4172,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f2314])).

fof(f2314,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1233])).

fof(f1233,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f5763,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl339_97 ),
    inference(avatar_component_clause,[],[f5761])).

fof(f5761,plain,
    ( spl339_97
  <=> m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_97])])).

fof(f74060,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k7_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK0)
    | ~ spl339_97 ),
    inference(resolution,[],[f5763,f4181])).

fof(f4181,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f2323])).

fof(f2323,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1258])).

fof(f1258,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f5769,plain,
    ( ~ spl339_98
    | spl339_1
    | ~ spl339_85 ),
    inference(avatar_split_clause,[],[f5759,f5667,f4720,f5766])).

fof(f4720,plain,
    ( spl339_1
  <=> sK0 = k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_1])])).

fof(f5667,plain,
    ( spl339_85
  <=> k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_85])])).

fof(f5759,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1))
    | spl339_1
    | ~ spl339_85 ),
    inference(backward_demodulation,[],[f4722,f5669])).

fof(f5669,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ spl339_85 ),
    inference(avatar_component_clause,[],[f5667])).

fof(f4722,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    | spl339_1 ),
    inference(avatar_component_clause,[],[f4720])).

fof(f5764,plain,
    ( spl339_97
    | ~ spl339_85
    | ~ spl339_88 ),
    inference(avatar_split_clause,[],[f5758,f5685,f5667,f5761])).

fof(f5685,plain,
    ( spl339_88
  <=> m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_88])])).

fof(f5758,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl339_85
    | ~ spl339_88 ),
    inference(backward_demodulation,[],[f5687,f5669])).

fof(f5687,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl339_88 ),
    inference(avatar_component_clause,[],[f5685])).

fof(f5725,plain,
    ( spl339_92
    | ~ spl339_3
    | ~ spl339_5 ),
    inference(avatar_split_clause,[],[f5720,f4740,f4730,f5722])).

fof(f4730,plain,
    ( spl339_3
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_3])])).

fof(f4740,plain,
    ( spl339_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_5])])).

fof(f5720,plain,
    ( sK0 = k9_relat_1(sK1,sK0)
    | ~ spl339_3
    | ~ spl339_5 ),
    inference(forward_demodulation,[],[f5719,f4732])).

fof(f4732,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl339_3 ),
    inference(avatar_component_clause,[],[f4730])).

fof(f5719,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0)
    | ~ spl339_5 ),
    inference(forward_demodulation,[],[f5506,f5388])).

fof(f5388,plain,
    ( ! [X0] : k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0)
    | ~ spl339_5 ),
    inference(unit_resulting_resolution,[],[f4742,f4172])).

fof(f4742,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl339_5 ),
    inference(avatar_component_clause,[],[f4740])).

fof(f5506,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)
    | ~ spl339_5 ),
    inference(resolution,[],[f4742,f4181])).

fof(f5688,plain,
    ( spl339_88
    | ~ spl339_4
    | ~ spl339_5 ),
    inference(avatar_split_clause,[],[f5358,f4740,f4735,f5685])).

fof(f4735,plain,
    ( spl339_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_4])])).

fof(f5358,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl339_4
    | ~ spl339_5 ),
    inference(unit_resulting_resolution,[],[f4737,f4742,f2865])).

fof(f2865,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1566])).

fof(f1566,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1565])).

fof(f1565,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1218])).

fof(f1218,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f4737,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl339_4 ),
    inference(avatar_component_clause,[],[f4735])).

fof(f5670,plain,
    ( spl339_85
    | ~ spl339_4
    | ~ spl339_5 ),
    inference(avatar_split_clause,[],[f5372,f4740,f4735,f5667])).

fof(f5372,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ spl339_4
    | ~ spl339_5 ),
    inference(unit_resulting_resolution,[],[f4737,f4742,f2866])).

fof(f2866,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f1568])).

fof(f1568,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1567])).

fof(f1567,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1230])).

fof(f1230,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f5641,plain,
    ( spl339_69
    | ~ spl339_5 ),
    inference(avatar_split_clause,[],[f5387,f4740,f5575])).

fof(f5387,plain,
    ( v1_relat_1(sK1)
    | ~ spl339_5 ),
    inference(unit_resulting_resolution,[],[f4742,f2946])).

fof(f2946,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1622])).

fof(f1622,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f5235,plain,
    ( spl339_50
    | ~ spl339_2
    | ~ spl339_4 ),
    inference(avatar_split_clause,[],[f5230,f4735,f4725,f5232])).

fof(f4725,plain,
    ( spl339_2
  <=> sK0 = k2_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl339_2])])).

fof(f5230,plain,
    ( sK0 = k9_relat_1(sK2,sK0)
    | ~ spl339_2
    | ~ spl339_4 ),
    inference(forward_demodulation,[],[f5229,f4727])).

fof(f4727,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK2)
    | ~ spl339_2 ),
    inference(avatar_component_clause,[],[f4725])).

fof(f5229,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0)
    | ~ spl339_4 ),
    inference(forward_demodulation,[],[f5031,f4913])).

fof(f4913,plain,
    ( ! [X0] : k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl339_4 ),
    inference(unit_resulting_resolution,[],[f4737,f4172])).

fof(f5031,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0)
    | ~ spl339_4 ),
    inference(resolution,[],[f4737,f4181])).

fof(f5171,plain,
    ( spl339_30
    | ~ spl339_4 ),
    inference(avatar_split_clause,[],[f4912,f4735,f5100])).

fof(f4912,plain,
    ( v1_relat_1(sK2)
    | ~ spl339_4 ),
    inference(unit_resulting_resolution,[],[f4737,f2946])).

fof(f4743,plain,(
    spl339_5 ),
    inference(avatar_split_clause,[],[f2860,f4740])).

fof(f2860,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f2395])).

fof(f2395,plain,
    ( sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1))
    & sK0 = k2_relset_1(sK0,sK0,sK2)
    & sK0 = k2_relset_1(sK0,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1564,f2394,f2393])).

fof(f2393,plain,
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

fof(f2394,plain,
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

fof(f1564,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f1563])).

fof(f1563,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1548])).

fof(f1548,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1547])).

fof(f1547,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

fof(f4738,plain,(
    spl339_4 ),
    inference(avatar_split_clause,[],[f2861,f4735])).

fof(f2861,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f2395])).

fof(f4733,plain,(
    spl339_3 ),
    inference(avatar_split_clause,[],[f2862,f4730])).

fof(f2862,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f2395])).

fof(f4728,plain,(
    spl339_2 ),
    inference(avatar_split_clause,[],[f2863,f4725])).

fof(f2863,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK2) ),
    inference(cnf_transformation,[],[f2395])).

fof(f4723,plain,(
    ~ spl339_1 ),
    inference(avatar_split_clause,[],[f2864,f4720])).

fof(f2864,plain,(
    sK0 != k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f2395])).
%------------------------------------------------------------------------------
