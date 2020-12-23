%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t143_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:31 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  346 ( 937 expanded)
%              Number of leaves         :   94 ( 398 expanded)
%              Depth                    :   14
%              Number of atoms          : 1114 (2816 expanded)
%              Number of equality atoms :   50 ( 182 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f728,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f89,f96,f103,f110,f117,f124,f131,f147,f154,f163,f173,f174,f187,f194,f201,f208,f215,f236,f252,f254,f256,f257,f258,f269,f276,f287,f298,f300,f311,f313,f324,f331,f345,f361,f377,f390,f416,f436,f437,f478,f491,f498,f505,f546,f552,f566,f586,f607,f616,f646,f653,f660,f667,f674,f681,f688,f695,f702,f709,f711,f713,f715,f717,f724,f727])).

fof(f727,plain,
    ( spl6_96
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f726,f541,f129,f122,f115,f550])).

fof(f550,plain,
    ( spl6_96
  <=> ! [X1] :
        ( ~ v1_funct_2(X1,sK0,sK0)
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ r1_partfun1(X1,sK2)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f115,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f122,plain,
    ( spl6_12
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f129,plain,
    ( spl6_14
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f541,plain,
    ( spl6_92
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f726,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,sK0)
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK2) )
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f725,f130])).

fof(f130,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f725,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,sK0)
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK2) )
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f719,f123])).

fof(f123,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f719,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,sK0,sK0)
        | ~ v1_funct_2(X1,sK0,sK0)
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK2) )
    | ~ spl6_10
    | ~ spl6_92 ),
    inference(resolution,[],[f639,f116])).

fof(f116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f639,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X3,sK0,X1)
        | ~ v1_funct_2(X2,sK0,X1)
        | r2_relset_1(sK0,X1,X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(X2)
        | ~ r1_partfun1(X2,X3) )
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f638,f542])).

fof(f542,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f541])).

fof(f638,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_funct_2(X3,sK0,X1)
        | ~ v1_funct_2(X2,sK0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(X2)
        | ~ r1_partfun1(X2,X3)
        | r2_relset_1(k1_xboole_0,X1,X2,X3) )
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f637,f542])).

fof(f637,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_funct_2(X2,sK0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ v1_funct_1(X2)
        | ~ r1_partfun1(X2,X3)
        | r2_relset_1(k1_xboole_0,X1,X2,X3) )
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f636,f542])).

fof(f636,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ v1_funct_1(X2)
        | ~ r1_partfun1(X2,X3)
        | r2_relset_1(k1_xboole_0,X1,X2,X3) )
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f619,f542])).

fof(f619,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_2(X2,k1_xboole_0,X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X1)
        | ~ v1_funct_1(X2)
        | ~ r1_partfun1(X2,X3)
        | r2_relset_1(k1_xboole_0,X1,X2,X3) )
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f70])).

fof(f70,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ r1_partfun1(X2,X3)
      | r2_relset_1(k1_xboole_0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 != X0
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',t142_funct_2)).

fof(f724,plain,
    ( spl6_94
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f723,f541,f94,f87,f80,f544])).

fof(f544,plain,
    ( spl6_94
  <=> ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK0)
        | r2_relset_1(sK0,sK0,X0,sK1)
        | ~ r1_partfun1(X0,sK1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f80,plain,
    ( spl6_0
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f87,plain,
    ( spl6_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f94,plain,
    ( spl6_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f723,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK0)
        | r2_relset_1(sK0,sK0,X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK1) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f722,f95])).

fof(f95,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f722,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK0)
        | r2_relset_1(sK0,sK0,X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK1) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f718,f88])).

fof(f88,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f718,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | r2_relset_1(sK0,sK0,X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK1) )
    | ~ spl6_0
    | ~ spl6_92 ),
    inference(resolution,[],[f639,f81])).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f80])).

fof(f717,plain,
    ( ~ spl6_115
    | spl6_27
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f716,f541,f185,f648])).

fof(f648,plain,
    ( spl6_115
  <=> ~ r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f185,plain,
    ( spl6_27
  <=> ~ r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f716,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl6_27
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f186,f542])).

fof(f186,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f185])).

fof(f715,plain,
    ( ~ spl6_117
    | spl6_29
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f714,f541,f192,f655])).

fof(f655,plain,
    ( spl6_117
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f192,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f714,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl6_29
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f193,f542])).

fof(f193,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f192])).

fof(f713,plain,
    ( ~ spl6_121
    | spl6_33
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f712,f541,f203,f669])).

fof(f669,plain,
    ( spl6_121
  <=> ~ m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f203,plain,
    ( spl6_33
  <=> ~ m1_subset_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f712,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl6_33
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f204,f542])).

fof(f204,plain,
    ( ~ m1_subset_1(sK2,k1_xboole_0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f203])).

fof(f711,plain,
    ( ~ spl6_123
    | spl6_35
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f710,f541,f210,f676])).

fof(f676,plain,
    ( spl6_123
  <=> ~ m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f210,plain,
    ( spl6_35
  <=> ~ m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f710,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ spl6_35
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f211,f542])).

fof(f211,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f210])).

fof(f709,plain,
    ( ~ spl6_131
    | spl6_47
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f631,f541,f285,f707])).

fof(f707,plain,
    ( spl6_131
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

fof(f285,plain,
    ( spl6_47
  <=> ~ r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f631,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl6_47
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f286])).

fof(f286,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f285])).

fof(f702,plain,
    ( ~ spl6_129
    | spl6_45
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f630,f541,f274,f700])).

fof(f700,plain,
    ( spl6_129
  <=> ~ sP5(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f274,plain,
    ( spl6_45
  <=> ~ sP5(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f630,plain,
    ( ~ sP5(sK0)
    | ~ spl6_45
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f275])).

fof(f275,plain,
    ( ~ sP5(k1_xboole_0)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f274])).

fof(f695,plain,
    ( ~ spl6_127
    | spl6_43
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f629,f541,f267,f693])).

fof(f693,plain,
    ( spl6_127
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).

fof(f267,plain,
    ( spl6_43
  <=> ~ r2_hidden(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f629,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl6_43
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f268])).

fof(f268,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f267])).

fof(f688,plain,
    ( ~ spl6_125
    | spl6_41
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f628,f541,f247,f686])).

fof(f686,plain,
    ( spl6_125
  <=> sK0 != sK3(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f247,plain,
    ( spl6_41
  <=> k1_xboole_0 != sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f628,plain,
    ( sK0 != sK3(k1_zfmisc_1(sK0))
    | ~ spl6_41
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f248])).

fof(f248,plain,
    ( k1_xboole_0 != sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f247])).

fof(f681,plain,
    ( spl6_122
    | ~ spl6_34
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f625,f541,f213,f679])).

fof(f679,plain,
    ( spl6_122
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f213,plain,
    ( spl6_34
  <=> m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f625,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl6_34
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f214])).

fof(f214,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f213])).

fof(f674,plain,
    ( spl6_120
    | ~ spl6_32
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f624,f541,f206,f672])).

fof(f672,plain,
    ( spl6_120
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f206,plain,
    ( spl6_32
  <=> m1_subset_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f624,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl6_32
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f207])).

fof(f207,plain,
    ( m1_subset_1(sK2,k1_xboole_0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f206])).

fof(f667,plain,
    ( ~ spl6_119
    | spl6_31
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f623,f541,f196,f665])).

fof(f665,plain,
    ( spl6_119
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f196,plain,
    ( spl6_31
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f623,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_31
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f197])).

fof(f197,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f196])).

fof(f660,plain,
    ( spl6_116
    | ~ spl6_28
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f622,f541,f189,f658])).

fof(f658,plain,
    ( spl6_116
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f189,plain,
    ( spl6_28
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f622,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_28
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f190])).

fof(f190,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f189])).

fof(f653,plain,
    ( spl6_114
    | ~ spl6_26
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f621,f541,f182,f651])).

fof(f651,plain,
    ( spl6_114
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f182,plain,
    ( spl6_26
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f621,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_26
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f183])).

fof(f183,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f182])).

fof(f646,plain,
    ( ~ spl6_113
    | spl6_23
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f620,f541,f158,f644])).

fof(f644,plain,
    ( spl6_113
  <=> k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f158,plain,
    ( spl6_23
  <=> k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f620,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != sK0
    | ~ spl6_23
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f542,f159])).

fof(f159,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_xboole_0
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f158])).

fof(f616,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | spl6_7
    | ~ spl6_8
    | ~ spl6_96 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f614,f88])).

fof(f614,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f613,f95])).

fof(f613,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_0
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f612,f109])).

fof(f109,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_8
  <=> r1_partfun1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f612,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_0
    | ~ spl6_7
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f608,f102])).

fof(f102,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl6_7
  <=> ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f608,plain,
    ( r2_relset_1(sK0,sK0,sK1,sK2)
    | ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_0
    | ~ spl6_96 ),
    inference(resolution,[],[f551,f81])).

fof(f551,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,X1,sK2)
        | ~ r1_partfun1(X1,sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0) )
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f550])).

fof(f607,plain,
    ( ~ spl6_107
    | ~ spl6_109
    | ~ spl6_111
    | spl6_81
    | spl6_83
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f588,f544,f473,f470,f605,f599,f593])).

fof(f593,plain,
    ( spl6_107
  <=> ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f599,plain,
    ( spl6_109
  <=> ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f605,plain,
    ( spl6_111
  <=> ~ r1_partfun1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f470,plain,
    ( spl6_81
  <=> ~ r2_relset_1(sK0,sK0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f473,plain,
    ( spl6_83
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f588,plain,
    ( ~ r1_partfun1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1)
    | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))))
    | ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK0,sK0)
    | ~ spl6_81
    | ~ spl6_83
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f587,f474])).

fof(f474,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f473])).

fof(f587,plain,
    ( ~ r1_partfun1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1)
    | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))))
    | ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK0,sK0)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ spl6_81
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f556,f471])).

fof(f471,plain,
    ( ~ r2_relset_1(sK0,sK0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1)
    | ~ spl6_81 ),
    inference(avatar_component_clause,[],[f470])).

fof(f556,plain,
    ( r2_relset_1(sK0,sK0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1)
    | ~ r1_partfun1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1)
    | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))))
    | ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK0,sK0)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ spl6_94 ),
    inference(resolution,[],[f545,f447])).

fof(f447,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f393,f134])).

fof(f134,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f65,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',existence_m1_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',t2_subset)).

fof(f393,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f66,f58])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',t4_subset)).

fof(f545,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r2_relset_1(sK0,sK0,X0,sK1)
        | ~ r1_partfun1(X0,sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0) )
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f544])).

fof(f586,plain,
    ( ~ spl6_101
    | ~ spl6_103
    | ~ spl6_105
    | spl6_63
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f567,f544,f369,f584,f578,f572])).

fof(f572,plain,
    ( spl6_101
  <=> ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f578,plain,
    ( spl6_103
  <=> ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f584,plain,
    ( spl6_105
  <=> ~ r1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f369,plain,
    ( spl6_63
  <=> ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f567,plain,
    ( ~ r1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1)
    | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK0,sK0)
    | ~ spl6_63
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f555,f370])).

fof(f370,plain,
    ( ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1)
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f369])).

fof(f555,plain,
    ( r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1)
    | ~ r1_partfun1(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1)
    | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK0,sK0)
    | ~ spl6_94 ),
    inference(resolution,[],[f545,f58])).

fof(f566,plain,
    ( ~ spl6_99
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | spl6_67
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f559,f544,f382,f129,f122,f115,f564])).

fof(f564,plain,
    ( spl6_99
  <=> ~ r1_partfun1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f382,plain,
    ( spl6_67
  <=> ~ r2_relset_1(sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f559,plain,
    ( ~ r1_partfun1(sK2,sK1)
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14
    | ~ spl6_67
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f558,f123])).

fof(f558,plain,
    ( ~ r1_partfun1(sK2,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_67
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f557,f130])).

fof(f557,plain,
    ( ~ r1_partfun1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ spl6_10
    | ~ spl6_67
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f554,f383])).

fof(f383,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK1)
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f382])).

fof(f554,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK1)
    | ~ r1_partfun1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ spl6_10
    | ~ spl6_94 ),
    inference(resolution,[],[f545,f116])).

fof(f552,plain,
    ( spl6_92
    | spl6_96
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f548,f129,f122,f115,f550,f541])).

fof(f548,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK2)
        | k1_xboole_0 = sK0
        | r2_relset_1(sK0,sK0,X1,sK2) )
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f547,f123])).

fof(f547,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK2)
        | k1_xboole_0 = sK0
        | r2_relset_1(sK0,sK0,X1,sK2) )
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f532,f130])).

fof(f532,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK2)
        | k1_xboole_0 = sK0
        | r2_relset_1(sK0,sK0,X1,sK2) )
    | ~ spl6_10 ),
    inference(resolution,[],[f59,f116])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f546,plain,
    ( spl6_92
    | spl6_94
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f536,f94,f87,f80,f544,f541])).

fof(f536,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK1)
        | k1_xboole_0 = sK0
        | r2_relset_1(sK0,sK0,X0,sK1) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f535,f88])).

fof(f535,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK1)
        | k1_xboole_0 = sK0
        | r2_relset_1(sK0,sK0,X0,sK1) )
    | ~ spl6_0
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f531,f95])).

fof(f531,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK1)
        | ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(X0,sK1)
        | k1_xboole_0 = sK0
        | r2_relset_1(sK0,sK0,X0,sK1) )
    | ~ spl6_0 ),
    inference(resolution,[],[f59,f81])).

fof(f505,plain,
    ( ~ spl6_87
    | spl6_90
    | spl6_82
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f456,f115,f476,f503,f489])).

fof(f489,plain,
    ( spl6_87
  <=> ~ r2_relset_1(sK0,sK0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f503,plain,
    ( spl6_90
  <=> sK2 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f476,plain,
    ( spl6_82
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f456,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | sK2 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ r2_relset_1(sK0,sK0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f447,f333])).

fof(f333,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | sK2 = X3
        | ~ r2_relset_1(sK0,sK0,X3,sK2) )
    | ~ spl6_10 ),
    inference(resolution,[],[f55,f116])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',redefinition_r2_relset_1)).

fof(f498,plain,
    ( ~ spl6_81
    | spl6_88
    | spl6_82
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f455,f80,f476,f496,f470])).

fof(f496,plain,
    ( spl6_88
  <=> sK1 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f455,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | sK1 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ r2_relset_1(sK0,sK0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1)
    | ~ spl6_0 ),
    inference(resolution,[],[f447,f334])).

fof(f334,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | sK1 = X4
        | ~ r2_relset_1(sK0,sK0,X4,sK1) )
    | ~ spl6_0 ),
    inference(resolution,[],[f55,f81])).

fof(f491,plain,
    ( spl6_84
    | ~ spl6_87
    | spl6_82
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f454,f115,f476,f489,f483])).

fof(f483,plain,
    ( spl6_84
  <=> r2_relset_1(sK0,sK0,sK2,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f454,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ r2_relset_1(sK0,sK0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK2)
    | r2_relset_1(sK0,sK0,sK2,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))))
    | ~ spl6_10 ),
    inference(resolution,[],[f447,f397])).

fof(f397,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r2_relset_1(sK0,sK0,X3,sK2)
        | r2_relset_1(sK0,sK0,sK2,X3) )
    | ~ spl6_10 ),
    inference(resolution,[],[f56,f116])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | r2_relset_1(X0,X1,X3,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',symmetry_r2_relset_1)).

fof(f478,plain,
    ( spl6_78
    | ~ spl6_81
    | spl6_82
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f453,f80,f476,f470,f464])).

fof(f464,plain,
    ( spl6_78
  <=> r2_relset_1(sK0,sK0,sK1,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f453,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ r2_relset_1(sK0,sK0,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),sK1)
    | r2_relset_1(sK0,sK0,sK1,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))))
    | ~ spl6_0 ),
    inference(resolution,[],[f447,f398])).

fof(f398,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r2_relset_1(sK0,sK0,X4,sK1)
        | r2_relset_1(sK0,sK0,sK1,X4) )
    | ~ spl6_0 ),
    inference(resolution,[],[f56,f81])).

fof(f437,plain,
    ( ~ spl6_77
    | ~ spl6_10
    | spl6_37 ),
    inference(avatar_split_clause,[],[f423,f231,f115,f434])).

fof(f434,plain,
    ( spl6_77
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f231,plain,
    ( spl6_37
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f423,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_10
    | ~ spl6_37 ),
    inference(duplicate_literal_removal,[],[f422])).

fof(f422,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_10
    | ~ spl6_37 ),
    inference(resolution,[],[f403,f400])).

fof(f400,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_10
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f399,f232])).

fof(f232,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f231])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK0)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f394,f65])).

fof(f394,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl6_10 ),
    inference(resolution,[],[f66,f116])).

fof(f403,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),X0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_10
    | ~ spl6_37 ),
    inference(resolution,[],[f400,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',antisymmetry_r2_hidden)).

fof(f436,plain,
    ( ~ spl6_75
    | ~ spl6_77
    | ~ spl6_0
    | ~ spl6_10
    | spl6_37 ),
    inference(avatar_split_clause,[],[f421,f231,f115,f80,f434,f428])).

fof(f428,plain,
    ( spl6_75
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f421,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl6_0
    | ~ spl6_10
    | ~ spl6_37 ),
    inference(resolution,[],[f403,f402])).

fof(f402,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_0
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f401,f232])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK0)) )
    | ~ spl6_0 ),
    inference(resolution,[],[f395,f65])).

fof(f395,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl6_0 ),
    inference(resolution,[],[f66,f81])).

fof(f416,plain,
    ( ~ spl6_71
    | spl6_72
    | ~ spl6_10
    | spl6_37 ),
    inference(avatar_split_clause,[],[f405,f231,f115,f414,f411])).

fof(f411,plain,
    ( spl6_71
  <=> ~ sP5(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f414,plain,
    ( spl6_72
  <=> ! [X2] : ~ r2_hidden(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f405,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ sP5(k2_zfmisc_1(sK0,sK0)) )
    | ~ spl6_10
    | ~ spl6_37 ),
    inference(resolution,[],[f400,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f63,f73_D])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f73_D])).

fof(f73_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',t5_subset)).

fof(f390,plain,
    ( ~ spl6_67
    | spl6_68
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f363,f115,f80,f388,f382])).

fof(f388,plain,
    ( spl6_68
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f363,plain,
    ( sK1 = sK2
    | ~ r2_relset_1(sK0,sK0,sK2,sK1)
    | ~ spl6_0
    | ~ spl6_10 ),
    inference(resolution,[],[f334,f116])).

fof(f377,plain,
    ( ~ spl6_63
    | spl6_64
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f362,f80,f375,f369])).

fof(f375,plain,
    ( spl6_64
  <=> sK1 = sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f362,plain,
    ( sK1 = sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1)
    | ~ spl6_0 ),
    inference(resolution,[],[f334,f58])).

fof(f361,plain,
    ( ~ spl6_59
    | spl6_60
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f346,f115,f359,f353])).

fof(f353,plain,
    ( spl6_59
  <=> ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f359,plain,
    ( spl6_60
  <=> sK2 = sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f346,plain,
    ( sK2 = sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f333,f58])).

fof(f345,plain,
    ( ~ spl6_57
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f335,f152,f343])).

fof(f343,plain,
    ( spl6_57
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f152,plain,
    ( spl6_20
  <=> r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f335,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f153,f68])).

fof(f153,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f331,plain,
    ( ~ spl6_55
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f316,f139,f329])).

fof(f329,plain,
    ( spl6_55
  <=> ~ sP5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f139,plain,
    ( spl6_16
  <=> r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f316,plain,
    ( ~ sP5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_16 ),
    inference(resolution,[],[f140,f74])).

fof(f140,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f324,plain,
    ( ~ spl6_53
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f314,f139,f322])).

fof(f322,plain,
    ( spl6_53
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f314,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl6_16 ),
    inference(resolution,[],[f140,f68])).

fof(f313,plain,
    ( spl6_20
    | ~ spl6_10
    | spl6_19 ),
    inference(avatar_split_clause,[],[f312,f142,f115,f152])).

fof(f142,plain,
    ( spl6_19
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f312,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f304,f143])).

fof(f143,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f142])).

fof(f304,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_10 ),
    inference(resolution,[],[f116,f65])).

fof(f311,plain,
    ( spl6_50
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f301,f115,f309])).

fof(f309,plain,
    ( spl6_50
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f301,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f116,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f300,plain,
    ( spl6_16
    | ~ spl6_0
    | spl6_19 ),
    inference(avatar_split_clause,[],[f299,f142,f80,f139])).

fof(f299,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_0
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f291,f143])).

fof(f291,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_0 ),
    inference(resolution,[],[f81,f65])).

fof(f298,plain,
    ( spl6_48
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f288,f80,f296])).

fof(f296,plain,
    ( spl6_48
  <=> r2_relset_1(sK0,sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f288,plain,
    ( r2_relset_1(sK0,sK0,sK1,sK1)
    | ~ spl6_0 ),
    inference(resolution,[],[f81,f75])).

fof(f287,plain,
    ( ~ spl6_47
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f277,f189,f285])).

fof(f277,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl6_28 ),
    inference(resolution,[],[f190,f68])).

fof(f276,plain,
    ( ~ spl6_45
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f261,f182,f274])).

fof(f261,plain,
    ( ~ sP5(k1_xboole_0)
    | ~ spl6_26 ),
    inference(resolution,[],[f183,f74])).

fof(f269,plain,
    ( ~ spl6_43
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f259,f182,f267])).

fof(f259,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2)
    | ~ spl6_26 ),
    inference(resolution,[],[f183,f68])).

fof(f258,plain,
    ( spl6_28
    | spl6_30
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f219,f213,f199,f189])).

fof(f199,plain,
    ( spl6_30
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f219,plain,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(sK1,k1_xboole_0)
    | ~ spl6_34 ),
    inference(resolution,[],[f214,f65])).

fof(f257,plain,
    ( spl6_26
    | spl6_30
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f218,f206,f199,f182])).

fof(f218,plain,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_32 ),
    inference(resolution,[],[f207,f65])).

fof(f256,plain,
    ( spl6_30
    | spl6_27
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f255,f206,f185,f199])).

fof(f255,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_27
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f218,f186])).

fof(f254,plain,
    ( spl6_30
    | spl6_29
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f253,f213,f192,f199])).

fof(f253,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_29
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f219,f193])).

fof(f252,plain,
    ( spl6_40
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f244,f199,f250])).

fof(f250,plain,
    ( spl6_40
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f244,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_30 ),
    inference(resolution,[],[f242,f200])).

fof(f200,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f199])).

fof(f242,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | k1_xboole_0 = sK3(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f237,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',t6_boole)).

fof(f237,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f225,f223])).

fof(f223,plain,(
    ! [X2] :
      ( ~ sP5(X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f134,f74])).

fof(f225,plain,(
    ! [X0] :
      ( sP5(sK3(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f73,f58])).

fof(f236,plain,
    ( ~ spl6_37
    | spl6_38
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f226,f161,f234,f231])).

fof(f234,plain,
    ( spl6_38
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | sP5(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f161,plain,
    ( spl6_22
  <=> k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | sP5(X0) )
    | ~ spl6_22 ),
    inference(superposition,[],[f73,f162])).

fof(f162,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_xboole_0
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f161])).

fof(f215,plain,
    ( spl6_34
    | ~ spl6_0
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f179,f161,f80,f213])).

fof(f179,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f162,f81])).

fof(f208,plain,
    ( spl6_32
    | ~ spl6_10
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f178,f161,f115,f206])).

fof(f178,plain,
    ( m1_subset_1(sK2,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f162,f116])).

fof(f201,plain,
    ( spl6_30
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f177,f161,f145,f199])).

fof(f145,plain,
    ( spl6_18
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f177,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f162,f146])).

fof(f146,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f194,plain,
    ( ~ spl6_29
    | spl6_17
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f176,f161,f136,f192])).

fof(f136,plain,
    ( spl6_17
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f176,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl6_17
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f162,f137])).

fof(f137,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f136])).

fof(f187,plain,
    ( ~ spl6_27
    | spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f175,f161,f149,f185])).

fof(f149,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f175,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f162,f150])).

fof(f150,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f149])).

fof(f174,plain,
    ( ~ spl6_25
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f165,f115,f171])).

fof(f171,plain,
    ( spl6_25
  <=> ~ sP4(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f165,plain,
    ( ~ sP4(sK0,sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f72,f116])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP4(X1,X0) ) ),
    inference(general_splitting,[],[f57,f71_D])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f71_D])).

fof(f71_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',reflexivity_r2_relset_1)).

fof(f173,plain,
    ( ~ spl6_25
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f164,f80,f171])).

fof(f164,plain,
    ( ~ sP4(sK0,sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f72,f81])).

fof(f163,plain,
    ( spl6_22
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f156,f145,f161])).

fof(f156,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_xboole_0
    | ~ spl6_18 ),
    inference(resolution,[],[f146,f62])).

fof(f154,plain,
    ( spl6_20
    | spl6_18
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f133,f115,f145,f152])).

fof(f133,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_10 ),
    inference(resolution,[],[f65,f116])).

fof(f147,plain,
    ( spl6_16
    | spl6_18
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f132,f80,f145,f139])).

fof(f132,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_0 ),
    inference(resolution,[],[f65,f81])).

fof(f131,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f46,f129])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t143_funct_2.p',t143_funct_2)).

fof(f124,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f47,f122])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f117,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f48,f115])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f49,f108])).

fof(f49,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f50,f101])).

fof(f50,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f51,f94])).

fof(f51,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f52,f87])).

fof(f52,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f53,f80])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
