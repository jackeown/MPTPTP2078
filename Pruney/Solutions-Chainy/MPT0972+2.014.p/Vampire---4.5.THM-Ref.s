%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 289 expanded)
%              Number of leaves         :   41 ( 124 expanded)
%              Depth                    :    8
%              Number of atoms          :  452 (1022 expanded)
%              Number of equality atoms :  105 ( 198 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1572)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (1560)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (1553)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f864,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f110,f115,f135,f140,f170,f175,f304,f310,f311,f387,f395,f396,f409,f410,f488,f502,f720,f730,f739,f821,f827,f863])).

fof(f863,plain,
    ( spl7_81
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f859,f727,f713])).

fof(f713,plain,
    ( spl7_81
  <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f727,plain,
    ( spl7_84
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f859,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_84 ),
    inference(resolution,[],[f729,f30])).

fof(f30,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f729,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f727])).

fof(f827,plain,
    ( spl7_20
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f817,f97,f206])).

fof(f206,plain,
    ( spl7_20
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f97,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f817,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f99,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f99,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f821,plain,
    ( spl7_22
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f813,f97,f221])).

fof(f221,plain,
    ( spl7_22
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f813,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f99,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f739,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f730,plain,
    ( ~ spl7_33
    | ~ spl7_11
    | spl7_84
    | spl7_82
    | ~ spl7_7
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f709,f486,f107,f717,f727,f137,f307])).

fof(f307,plain,
    ( spl7_33
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f137,plain,
    ( spl7_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f717,plain,
    ( spl7_82
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f107,plain,
    ( spl7_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f486,plain,
    ( spl7_55
  <=> ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f709,plain,
    ( sK2 = sK3
    | r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | sK0 != k1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_55 ),
    inference(resolution,[],[f109,f487])).

fof(f487,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK2 = X0
        | r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 )
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f486])).

fof(f109,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f720,plain,
    ( ~ spl7_11
    | ~ spl7_33
    | ~ spl7_81
    | spl7_82
    | ~ spl7_7
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f707,f500,f107,f717,f713,f307,f137])).

fof(f500,plain,
    ( spl7_57
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f707,plain,
    ( sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK0 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_57 ),
    inference(resolution,[],[f109,f501])).

fof(f501,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0) )
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f500])).

fof(f502,plain,
    ( ~ spl7_10
    | spl7_57
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f498,f301,f87,f500,f132])).

fof(f132,plain,
    ( spl7_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f87,plain,
    ( spl7_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f301,plain,
    ( spl7_32
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f498,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0 )
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f496,f303])).

fof(f303,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f301])).

fof(f496,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0 )
    | ~ spl7_3 ),
    inference(resolution,[],[f41,f89])).

fof(f89,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f488,plain,
    ( ~ spl7_10
    | spl7_55
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f484,f301,f87,f486,f132])).

fof(f484,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | sK2 = X0 )
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f483,f303])).

fof(f483,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
        | sK2 = X0 )
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f481,f303])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
        | sK2 = X0 )
    | ~ spl7_3 ),
    inference(resolution,[],[f40,f89])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f410,plain,
    ( spl7_19
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f400,f77,f201])).

fof(f201,plain,
    ( spl7_19
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f77,plain,
    ( spl7_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f400,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f79,f75])).

fof(f79,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f409,plain,
    ( spl7_21
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f399,f77,f216])).

fof(f216,plain,
    ( spl7_21
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f399,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f79,f55])).

fof(f396,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != sK2
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f395,plain,
    ( spl7_46
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f390,f172,f112,f392])).

fof(f392,plain,
    ( spl7_46
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f112,plain,
    ( spl7_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f172,plain,
    ( spl7_16
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f390,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_8
    | ~ spl7_16 ),
    inference(resolution,[],[f288,f144])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f120,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f120,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_8 ),
    inference(resolution,[],[f117,f114])).

fof(f114,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f288,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl7_16 ),
    inference(resolution,[],[f174,f117])).

fof(f174,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f172])).

fof(f387,plain,
    ( spl7_45
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f382,f163,f112,f384])).

fof(f384,plain,
    ( spl7_45
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f163,plain,
    ( spl7_14
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f382,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(resolution,[],[f281,f144])).

fof(f281,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl7_14 ),
    inference(resolution,[],[f165,f117])).

fof(f165,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f311,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f310,plain,
    ( ~ spl7_6
    | spl7_31
    | spl7_33
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f305,f221,f97,f307,f297,f102])).

fof(f102,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f297,plain,
    ( spl7_31
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f305,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f291,f223])).

fof(f223,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f221])).

fof(f291,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f61,f99])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f304,plain,
    ( ~ spl7_2
    | spl7_31
    | spl7_32
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f295,f216,f77,f301,f297,f82])).

fof(f82,plain,
    ( spl7_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f295,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f290,f218])).

fof(f218,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f290,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f61,f79])).

fof(f175,plain,
    ( spl7_16
    | ~ spl7_15
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f159,f97,f167,f172])).

fof(f167,plain,
    ( spl7_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f159,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f44,f99])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f170,plain,
    ( spl7_14
    | ~ spl7_15
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f158,f77,f167,f163])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f44,f79])).

fof(f140,plain,
    ( spl7_11
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f123,f97,f137])).

fof(f123,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f54,f99])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f135,plain,
    ( spl7_10
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f122,f77,f132])).

fof(f122,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f54,f79])).

fof(f115,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f38,f112])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f110,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f31,f107])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f105,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f32,f102])).

fof(f32,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f100,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f33,f97])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f34,f92])).

fof(f92,plain,
    ( spl7_4
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f34,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f35,f87])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:55:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (1562)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (1570)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.49  % (1554)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (1547)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (1550)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (1551)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1561)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (1563)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (1564)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (1555)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (1565)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (1555)Refutation not found, incomplete strategy% (1555)------------------------------
% 0.21/0.54  % (1555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1555)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1555)Memory used [KB]: 10746
% 0.21/0.54  % (1555)Time elapsed: 0.129 s
% 0.21/0.54  % (1555)------------------------------
% 0.21/0.54  % (1555)------------------------------
% 0.21/0.54  % (1571)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (1563)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  % (1572)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (1560)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (1553)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  fof(f864,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f110,f115,f135,f140,f170,f175,f304,f310,f311,f387,f395,f396,f409,f410,f488,f502,f720,f730,f739,f821,f827,f863])).
% 0.21/0.54  fof(f863,plain,(
% 0.21/0.54    spl7_81 | ~spl7_84),
% 0.21/0.54    inference(avatar_split_clause,[],[f859,f727,f713])).
% 0.21/0.54  fof(f713,plain,(
% 0.21/0.54    spl7_81 <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).
% 0.21/0.54  fof(f727,plain,(
% 0.21/0.54    spl7_84 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 0.21/0.54  fof(f859,plain,(
% 0.21/0.54    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl7_84),
% 0.21/0.54    inference(resolution,[],[f729,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.54    inference(negated_conjecture,[],[f14])).
% 0.21/0.54  fof(f14,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 0.21/0.54  fof(f729,plain,(
% 0.21/0.54    r2_hidden(sK4(sK2,sK3),sK0) | ~spl7_84),
% 0.21/0.54    inference(avatar_component_clause,[],[f727])).
% 0.21/0.54  fof(f827,plain,(
% 0.21/0.54    spl7_20 | ~spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f817,f97,f206])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    spl7_20 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.54  fof(f817,plain,(
% 0.21/0.54    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl7_5),
% 0.21/0.54    inference(resolution,[],[f99,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.54    inference(equality_resolution,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f97])).
% 0.21/0.54  fof(f821,plain,(
% 0.21/0.54    spl7_22 | ~spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f813,f97,f221])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    spl7_22 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.54  fof(f813,plain,(
% 0.21/0.54    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl7_5),
% 0.21/0.54    inference(resolution,[],[f99,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f739,plain,(
% 0.21/0.54    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f730,plain,(
% 0.21/0.54    ~spl7_33 | ~spl7_11 | spl7_84 | spl7_82 | ~spl7_7 | ~spl7_55),
% 0.21/0.54    inference(avatar_split_clause,[],[f709,f486,f107,f717,f727,f137,f307])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    spl7_33 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    spl7_11 <=> v1_relat_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.54  fof(f717,plain,(
% 0.21/0.54    spl7_82 <=> sK2 = sK3),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    spl7_7 <=> v1_funct_1(sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.54  fof(f486,plain,(
% 0.21/0.54    spl7_55 <=> ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 0.21/0.54  fof(f709,plain,(
% 0.21/0.54    sK2 = sK3 | r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3) | sK0 != k1_relat_1(sK3) | (~spl7_7 | ~spl7_55)),
% 0.21/0.54    inference(resolution,[],[f109,f487])).
% 0.21/0.54  fof(f487,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_funct_1(X0) | sK2 = X0 | r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0) ) | ~spl7_55),
% 0.21/0.54    inference(avatar_component_clause,[],[f486])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    v1_funct_1(sK3) | ~spl7_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f107])).
% 0.21/0.54  fof(f720,plain,(
% 0.21/0.54    ~spl7_11 | ~spl7_33 | ~spl7_81 | spl7_82 | ~spl7_7 | ~spl7_57),
% 0.21/0.54    inference(avatar_split_clause,[],[f707,f500,f107,f717,f713,f307,f137])).
% 0.21/0.54  fof(f500,plain,(
% 0.21/0.54    spl7_57 <=> ! [X0] : (k1_relat_1(X0) != sK0 | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 0.21/0.55  fof(f707,plain,(
% 0.21/0.55    sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK3,sK4(sK2,sK3)) | sK0 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl7_7 | ~spl7_57)),
% 0.21/0.55    inference(resolution,[],[f109,f501])).
% 0.21/0.55  fof(f501,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_funct_1(X0) | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | k1_relat_1(X0) != sK0 | ~v1_relat_1(X0)) ) | ~spl7_57),
% 0.21/0.55    inference(avatar_component_clause,[],[f500])).
% 0.21/0.55  fof(f502,plain,(
% 0.21/0.55    ~spl7_10 | spl7_57 | ~spl7_3 | ~spl7_32),
% 0.21/0.55    inference(avatar_split_clause,[],[f498,f301,f87,f500,f132])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    spl7_10 <=> v1_relat_1(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    spl7_3 <=> v1_funct_1(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.55  fof(f301,plain,(
% 0.21/0.55    spl7_32 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.55  fof(f498,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0) ) | (~spl7_3 | ~spl7_32)),
% 0.21/0.55    inference(forward_demodulation,[],[f496,f303])).
% 0.21/0.55  fof(f303,plain,(
% 0.21/0.55    sK0 = k1_relat_1(sK2) | ~spl7_32),
% 0.21/0.55    inference(avatar_component_clause,[],[f301])).
% 0.21/0.55  fof(f496,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0) ) | ~spl7_3),
% 0.21/0.55    inference(resolution,[],[f41,f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    v1_funct_1(sK2) | ~spl7_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f87])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.55  fof(f488,plain,(
% 0.21/0.55    ~spl7_10 | spl7_55 | ~spl7_3 | ~spl7_32),
% 0.21/0.55    inference(avatar_split_clause,[],[f484,f301,f87,f486,f132])).
% 0.21/0.55  fof(f484,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | sK2 = X0) ) | (~spl7_3 | ~spl7_32)),
% 0.21/0.55    inference(forward_demodulation,[],[f483,f303])).
% 0.21/0.55  fof(f483,plain,(
% 0.21/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | sK2 = X0) ) | (~spl7_3 | ~spl7_32)),
% 0.21/0.55    inference(forward_demodulation,[],[f481,f303])).
% 0.21/0.55  fof(f481,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | sK2 = X0) ) | ~spl7_3),
% 0.21/0.55    inference(resolution,[],[f40,f89])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f410,plain,(
% 0.21/0.55    spl7_19 | ~spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f400,f77,f201])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    spl7_19 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    spl7_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.55  fof(f400,plain,(
% 0.21/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_1),
% 0.21/0.55    inference(resolution,[],[f79,f75])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f77])).
% 0.21/0.55  fof(f409,plain,(
% 0.21/0.55    spl7_21 | ~spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f399,f77,f216])).
% 0.21/0.55  fof(f216,plain,(
% 0.21/0.55    spl7_21 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.55  fof(f399,plain,(
% 0.21/0.55    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl7_1),
% 0.21/0.55    inference(resolution,[],[f79,f55])).
% 0.21/0.55  fof(f396,plain,(
% 0.21/0.55    k1_xboole_0 != sK3 | k1_xboole_0 != sK2 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.55  fof(f395,plain,(
% 0.21/0.55    spl7_46 | ~spl7_8 | ~spl7_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f390,f172,f112,f392])).
% 0.21/0.55  fof(f392,plain,(
% 0.21/0.55    spl7_46 <=> k1_xboole_0 = sK3),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    spl7_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    spl7_16 <=> v1_xboole_0(sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.55  fof(f390,plain,(
% 0.21/0.55    k1_xboole_0 = sK3 | (~spl7_8 | ~spl7_16)),
% 0.21/0.55    inference(resolution,[],[f288,f144])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl7_8),
% 0.21/0.55    inference(resolution,[],[f120,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_8),
% 0.21/0.55    inference(resolution,[],[f117,f114])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    v1_xboole_0(k1_xboole_0) | ~spl7_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f112])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f49,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f288,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl7_16),
% 0.21/0.55    inference(resolution,[],[f174,f117])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    v1_xboole_0(sK3) | ~spl7_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f172])).
% 0.21/0.55  fof(f387,plain,(
% 0.21/0.55    spl7_45 | ~spl7_8 | ~spl7_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f382,f163,f112,f384])).
% 0.21/0.55  fof(f384,plain,(
% 0.21/0.55    spl7_45 <=> k1_xboole_0 = sK2),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    spl7_14 <=> v1_xboole_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.55  fof(f382,plain,(
% 0.21/0.55    k1_xboole_0 = sK2 | (~spl7_8 | ~spl7_14)),
% 0.21/0.55    inference(resolution,[],[f281,f144])).
% 0.21/0.55  fof(f281,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl7_14),
% 0.21/0.55    inference(resolution,[],[f165,f117])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    v1_xboole_0(sK2) | ~spl7_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f163])).
% 0.21/0.55  fof(f311,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.55  fof(f310,plain,(
% 0.21/0.55    ~spl7_6 | spl7_31 | spl7_33 | ~spl7_5 | ~spl7_22),
% 0.21/0.55    inference(avatar_split_clause,[],[f305,f221,f97,f307,f297,f102])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    spl7_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.55  fof(f297,plain,(
% 0.21/0.55    spl7_31 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | (~spl7_5 | ~spl7_22)),
% 0.21/0.55    inference(forward_demodulation,[],[f291,f223])).
% 0.21/0.55  fof(f223,plain,(
% 0.21/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl7_22),
% 0.21/0.55    inference(avatar_component_clause,[],[f221])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl7_5),
% 0.21/0.55    inference(resolution,[],[f61,f99])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.55  fof(f304,plain,(
% 0.21/0.55    ~spl7_2 | spl7_31 | spl7_32 | ~spl7_1 | ~spl7_21),
% 0.21/0.55    inference(avatar_split_clause,[],[f295,f216,f77,f301,f297,f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    spl7_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.55  fof(f295,plain,(
% 0.21/0.55    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | (~spl7_1 | ~spl7_21)),
% 0.21/0.55    inference(forward_demodulation,[],[f290,f218])).
% 0.21/0.55  fof(f218,plain,(
% 0.21/0.55    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl7_21),
% 0.21/0.55    inference(avatar_component_clause,[],[f216])).
% 0.21/0.55  fof(f290,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl7_1),
% 0.21/0.55    inference(resolution,[],[f61,f79])).
% 0.21/0.55  fof(f175,plain,(
% 0.21/0.55    spl7_16 | ~spl7_15 | ~spl7_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f159,f97,f167,f172])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    spl7_15 <=> v1_xboole_0(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    ~v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~spl7_5),
% 0.21/0.55    inference(resolution,[],[f44,f99])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    spl7_14 | ~spl7_15 | ~spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f158,f77,f167,f163])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    ~v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~spl7_1),
% 0.21/0.55    inference(resolution,[],[f44,f79])).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    spl7_11 | ~spl7_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f123,f97,f137])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    v1_relat_1(sK3) | ~spl7_5),
% 0.21/0.55    inference(resolution,[],[f54,f99])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    spl7_10 | ~spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f122,f77,f132])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.55    inference(resolution,[],[f54,f79])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    spl7_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f38,f112])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    v1_xboole_0(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    spl7_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f31,f107])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    v1_funct_1(sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    spl7_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f32,f102])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    spl7_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f33,f97])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ~spl7_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f34,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    spl7_4 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl7_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f35,f87])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    v1_funct_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f36,f82])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f37,f77])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (1563)------------------------------
% 0.21/0.55  % (1563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1563)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (1563)Memory used [KB]: 11257
% 0.21/0.55  % (1563)Time elapsed: 0.130 s
% 0.21/0.55  % (1563)------------------------------
% 0.21/0.55  % (1563)------------------------------
% 0.21/0.55  % (1552)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (1546)Success in time 0.183 s
%------------------------------------------------------------------------------
