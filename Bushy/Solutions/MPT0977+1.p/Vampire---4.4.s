%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t23_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:42 EDT 2019

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 551 expanded)
%              Number of leaves         :   61 ( 239 expanded)
%              Depth                    :    9
%              Number of atoms          :  518 (1253 expanded)
%              Number of equality atoms :   53 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f127,f151,f155,f159,f163,f164,f168,f169,f173,f177,f181,f185,f189,f197,f198,f201,f205,f212,f222,f226,f227,f231,f236,f241,f246,f251,f256,f261,f266,f295,f299,f300,f304,f308,f312,f313,f317,f321,f325,f326,f330,f334,f338,f342,f347,f352,f357])).

fof(f357,plain,
    ( ~ spl6_81
    | spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f353,f125,f121,f355])).

fof(f355,plain,
    ( spl6_81
  <=> ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f121,plain,
    ( spl6_3
  <=> ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f125,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f353,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_relat_1(sK1)),sK2)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f122,f133])).

fof(f133,plain,
    ( ! [X0] : k4_relset_1(sK0,sK1,X0,X0,sK2,k6_relat_1(X0)) = k5_relat_1(sK2,k6_relat_1(X0))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f109,f126,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',redefinition_k4_relset_1)).

fof(f126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',redefinition_k6_partfun1)).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',dt_k6_partfun1)).

fof(f122,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f352,plain,
    ( spl6_78
    | ~ spl6_24
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f348,f254,f187,f350])).

fof(f350,plain,
    ( spl6_78
  <=> k5_relat_1(k6_relat_1(sK0),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f187,plain,
    ( spl6_24
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f254,plain,
    ( spl6_46
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f348,plain,
    ( k5_relat_1(k6_relat_1(sK0),sK2) = sK2
    | ~ spl6_24
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f188,f255,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',t77_relat_1)).

fof(f255,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f254])).

fof(f188,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f187])).

fof(f347,plain,
    ( ~ spl6_77
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f343,f125,f118,f345])).

fof(f345,plain,
    ( spl6_77
  <=> ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f118,plain,
    ( spl6_1
  <=> ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f343,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_relat_1(sK0),sK2),sK2)
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f136,f119])).

fof(f119,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f136,plain,
    ( ! [X0] : k4_relset_1(X0,X0,sK0,sK1,k6_relat_1(X0),sK2) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f109,f126,f106])).

fof(f342,plain,
    ( spl6_74
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f268,f264,f340])).

fof(f340,plain,
    ( spl6_74
  <=> k1_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)) = k1_relat_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f264,plain,
    ( spl6_50
  <=> m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f268,plain,
    ( k1_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)) = k1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',redefinition_k1_relset_1)).

fof(f265,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f264])).

fof(f338,plain,
    ( spl6_72
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f269,f264,f336])).

fof(f336,plain,
    ( spl6_72
  <=> k2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)) = k2_relat_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f269,plain,
    ( k2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)) = k2_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',redefinition_k2_relset_1)).

fof(f334,plain,
    ( spl6_70
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f270,f264,f332])).

fof(f332,plain,
    ( spl6_70
  <=> m1_subset_1(k2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f270,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK1))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',dt_k2_relset_1)).

fof(f330,plain,
    ( spl6_68
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f271,f264,f328])).

fof(f328,plain,
    ( spl6_68
  <=> m1_subset_1(k1_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f271,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK0))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',dt_k1_relset_1)).

fof(f326,plain,
    ( spl6_64
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f272,f264,f319])).

fof(f319,plain,
    ( spl6_64
  <=> k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f272,plain,
    ( k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f265,f106])).

fof(f325,plain,
    ( spl6_66
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f274,f264,f125,f323])).

fof(f323,plain,
    ( spl6_66
  <=> k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2) = k5_relat_1(k5_relat_1(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f274,plain,
    ( k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2) = k5_relat_1(k5_relat_1(sK2,sK2),sK2)
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f126,f265,f106])).

fof(f321,plain,
    ( spl6_64
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f276,f264,f319])).

fof(f276,plain,
    ( k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f265,f106])).

fof(f317,plain,
    ( spl6_62
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f278,f264,f125,f315])).

fof(f315,plain,
    ( spl6_62
  <=> k4_relset_1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)) = k5_relat_1(sK2,k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f278,plain,
    ( k4_relset_1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)) = k5_relat_1(sK2,k5_relat_1(sK2,sK2))
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f126,f265,f106])).

fof(f313,plain,
    ( spl6_58
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f280,f264,f306])).

fof(f306,plain,
    ( spl6_58
  <=> m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f280,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f265,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',dt_k4_relset_1)).

fof(f312,plain,
    ( spl6_60
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f282,f264,f125,f310])).

fof(f310,plain,
    ( spl6_60
  <=> m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f282,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f126,f265,f107])).

fof(f308,plain,
    ( spl6_58
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f284,f264,f306])).

fof(f284,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f265,f107])).

fof(f304,plain,
    ( spl6_56
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f286,f264,f125,f302])).

fof(f302,plain,
    ( spl6_56
  <=> m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f286,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f126,f265,f107])).

fof(f300,plain,
    ( spl6_54
    | spl6_11
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f288,f264,f157,f297])).

fof(f297,plain,
    ( spl6_54
  <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f157,plain,
    ( spl6_11
  <=> ~ sP5(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f288,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl6_11
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f158,f265,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP5(X1,X0) ) ),
    inference(cnf_transformation,[],[f114_D])).

fof(f114_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP5(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f158,plain,
    ( ~ sP5(sK1,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f299,plain,
    ( spl6_54
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f290,f264,f297])).

fof(f290,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',redefinition_r2_relset_1)).

fof(f295,plain,
    ( spl6_52
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f291,f264,f293])).

fof(f293,plain,
    ( spl6_52
  <=> r1_tarski(k5_relat_1(sK2,sK2),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f291,plain,
    ( r1_tarski(k5_relat_1(sK2,sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f265,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',t3_subset)).

fof(f266,plain,
    ( spl6_50
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f262,f166,f161,f264])).

fof(f161,plain,
    ( spl6_12
  <=> m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f166,plain,
    ( spl6_14
  <=> k4_relset_1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f262,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f162,f167])).

fof(f167,plain,
    ( k4_relset_1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f162,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f261,plain,
    ( spl6_48
    | ~ spl6_24
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f257,f244,f187,f259])).

fof(f259,plain,
    ( spl6_48
  <=> k5_relat_1(sK2,k6_relat_1(sK1)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f244,plain,
    ( spl6_42
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f257,plain,
    ( k5_relat_1(sK2,k6_relat_1(sK1)) = sK2
    | ~ spl6_24
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f188,f245,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',t79_relat_1)).

fof(f245,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f244])).

fof(f256,plain,
    ( spl6_46
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f252,f249,f254])).

fof(f249,plain,
    ( spl6_44
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f252,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl6_44 ),
    inference(unit_resulting_resolution,[],[f250,f92])).

fof(f250,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f249])).

fof(f251,plain,
    ( spl6_44
    | ~ spl6_16
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f247,f183,f171,f249])).

fof(f171,plain,
    ( spl6_16
  <=> m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f183,plain,
    ( spl6_22
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f247,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl6_16
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f184,f172])).

fof(f172,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f171])).

fof(f184,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f246,plain,
    ( spl6_42
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f242,f239,f244])).

fof(f239,plain,
    ( spl6_40
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f242,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f240,f92])).

fof(f240,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f239])).

fof(f241,plain,
    ( spl6_40
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f237,f179,f175,f239])).

fof(f175,plain,
    ( spl6_18
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f179,plain,
    ( spl6_20
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f237,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(backward_demodulation,[],[f180,f176])).

fof(f176,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f180,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f179])).

fof(f236,plain,
    ( spl6_38
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f232,f175,f234])).

fof(f234,plain,
    ( spl6_38
  <=> r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f232,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1)
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f176,f92])).

fof(f231,plain,
    ( spl6_36
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f214,f195,f187,f229])).

fof(f229,plain,
    ( spl6_36
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f195,plain,
    ( spl6_26
  <=> v1_relat_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f214,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),sK2))
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f188,f196,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',dt_k5_relat_1)).

fof(f196,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f195])).

fof(f227,plain,
    ( spl6_32
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f215,f195,f220])).

fof(f220,plain,
    ( spl6_32
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f215,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f196,f196,f91])).

fof(f226,plain,
    ( spl6_34
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f217,f195,f187,f224])).

fof(f224,plain,
    ( spl6_34
  <=> v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f217,plain,
    ( v1_relat_1(k5_relat_1(sK2,k5_relat_1(sK2,sK2)))
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f188,f196,f91])).

fof(f222,plain,
    ( spl6_32
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f218,f195,f220])).

fof(f218,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f196,f196,f91])).

fof(f212,plain,
    ( spl6_30
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f208,f171,f210])).

fof(f210,plain,
    ( spl6_30
  <=> r1_tarski(k1_relset_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f208,plain,
    ( r1_tarski(k1_relset_1(sK0,sK1,sK2),sK0)
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f172,f92])).

fof(f205,plain,
    ( spl6_28
    | spl6_11 ),
    inference(avatar_split_clause,[],[f199,f157,f203])).

fof(f203,plain,
    ( spl6_28
  <=> r2_relset_1(sK0,sK1,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f199,plain,
    ( r2_relset_1(sK0,sK1,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f85,f158,f114])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',existence_m1_subset_1)).

fof(f201,plain,
    ( spl6_8
    | ~ spl6_4
    | spl6_11 ),
    inference(avatar_split_clause,[],[f200,f157,f125,f153])).

fof(f153,plain,
    ( spl6_8
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f200,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f126,f158,f114])).

fof(f198,plain,
    ( spl6_26
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f191,f187,f195])).

fof(f191,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f188,f188,f91])).

fof(f197,plain,
    ( spl6_26
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f193,f187,f195])).

fof(f193,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f188,f188,f91])).

fof(f189,plain,
    ( spl6_24
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f128,f125,f187])).

fof(f128,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',cc1_relset_1)).

fof(f185,plain,
    ( spl6_22
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f129,f125,f183])).

fof(f129,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f96])).

fof(f181,plain,
    ( spl6_20
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f130,f125,f179])).

fof(f130,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f97])).

fof(f177,plain,
    ( spl6_18
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f131,f125,f175])).

fof(f131,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f98])).

fof(f173,plain,
    ( spl6_16
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f132,f125,f171])).

fof(f132,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f99])).

fof(f169,plain,
    ( spl6_14
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f135,f125,f166])).

fof(f135,plain,
    ( k4_relset_1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f126,f106])).

fof(f168,plain,
    ( spl6_14
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f138,f125,f166])).

fof(f138,plain,
    ( k4_relset_1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f126,f106])).

fof(f164,plain,
    ( spl6_12
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f141,f125,f161])).

fof(f141,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f126,f107])).

fof(f163,plain,
    ( spl6_12
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f144,f125,f161])).

fof(f144,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f126,f107])).

fof(f159,plain,
    ( ~ spl6_11
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f145,f125,f157])).

fof(f145,plain,
    ( ~ sP5(sK1,sK0)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f115])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f102,f114_D])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',reflexivity_r2_relset_1)).

fof(f155,plain,
    ( spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f146,f125,f153])).

fof(f146,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f116])).

fof(f151,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f147,f125,f149])).

fof(f149,plain,
    ( spl6_6
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f147,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f126,f92])).

fof(f127,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f77,f125])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f72])).

fof(f72,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t23_funct_2.p',t23_funct_2)).

fof(f123,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f108,f121,f118])).

fof(f108,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_relat_1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_relat_1(sK0),sK2),sK2) ),
    inference(definition_unfolding,[],[f78,f82,f82])).

fof(f78,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f73])).
%------------------------------------------------------------------------------
