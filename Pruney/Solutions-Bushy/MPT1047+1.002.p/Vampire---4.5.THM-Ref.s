%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1047+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:09 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 262 expanded)
%              Number of leaves         :   28 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  602 (1189 expanded)
%              Number of equality atoms :   92 ( 234 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1878,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f201,f216,f263,f680,f1056,f1740,f1798,f1877])).

fof(f1877,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | spl8_28
    | ~ spl8_47
    | ~ spl8_71
    | ~ spl8_76 ),
    inference(avatar_contradiction_clause,[],[f1876])).

fof(f1876,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | spl8_28
    | ~ spl8_47
    | ~ spl8_71
    | ~ spl8_76 ),
    inference(subsumption_resolution,[],[f1856,f1869])).

fof(f1869,plain,
    ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)),sK3)
    | ~ spl8_5
    | spl8_28
    | ~ spl8_76 ),
    inference(unit_resulting_resolution,[],[f122,f679,f1797,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1797,plain,
    ( m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f1795])).

fof(f1795,plain,
    ( spl8_76
  <=> m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f679,plain,
    ( sK3 != sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | spl8_28 ),
    inference(avatar_component_clause,[],[f677])).

fof(f677,plain,
    ( spl8_28
  <=> sK3 = sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1856,plain,
    ( r2_relset_1(sK0,k1_tarski(sK1),sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)),sK3)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_47
    | ~ spl8_71
    | ~ spl8_76 ),
    inference(unit_resulting_resolution,[],[f107,f112,f122,f1055,f1739,f1797,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r2_relset_1(X0,k1_tarski(X1),X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,k1_tarski(X1),X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_2(X3,X0,k1_tarski(X1))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X2,X0,k1_tarski(X1))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_2)).

fof(f1739,plain,
    ( v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)),sK0,k1_tarski(sK1))
    | ~ spl8_71 ),
    inference(avatar_component_clause,[],[f1737])).

fof(f1737,plain,
    ( spl8_71
  <=> v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)),sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f1055,plain,
    ( v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f1053,plain,
    ( spl8_47
  <=> v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f112,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_3
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f107,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1798,plain,
    ( spl8_76
    | ~ spl8_1
    | ~ spl8_4
    | spl8_6
    | spl8_28 ),
    inference(avatar_split_clause,[],[f1249,f677,f125,f115,f100,f1795])).

fof(f100,plain,
    ( spl8_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f115,plain,
    ( spl8_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f125,plain,
    ( spl8_6
  <=> k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1249,plain,
    ( m1_subset_1(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_1
    | ~ spl8_4
    | spl8_6
    | spl8_28 ),
    inference(unit_resulting_resolution,[],[f127,f679,f442])).

fof(f442,plain,
    ( ! [X2] :
        ( m1_subset_1(sK4(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | sK4(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2)) = X2
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f272,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f272,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) )
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f159,f117])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
        | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl8_1 ),
    inference(resolution,[],[f69,f102])).

fof(f102,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(f127,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1740,plain,
    ( spl8_71
    | ~ spl8_1
    | ~ spl8_4
    | spl8_6
    | spl8_28 ),
    inference(avatar_split_clause,[],[f1133,f677,f125,f115,f100,f1737])).

fof(f1133,plain,
    ( v1_funct_2(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)),sK0,k1_tarski(sK1))
    | ~ spl8_1
    | ~ spl8_4
    | spl8_6
    | spl8_28 ),
    inference(unit_resulting_resolution,[],[f127,f679,f411])).

fof(f411,plain,
    ( ! [X2] :
        ( v1_funct_2(sK4(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2)),sK0,k1_tarski(sK1))
        | sK4(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2)) = X2
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f270,f63])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_2(X0,sK0,k1_tarski(sK1)) )
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f157,f117])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
        | v1_funct_2(X0,X1,X2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f68,f102])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1056,plain,
    ( spl8_47
    | ~ spl8_1
    | ~ spl8_4
    | spl8_6
    | spl8_28 ),
    inference(avatar_split_clause,[],[f953,f677,f125,f115,f100,f1053])).

fof(f953,plain,
    ( v1_funct_1(sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)))
    | ~ spl8_1
    | ~ spl8_4
    | spl8_6
    | spl8_28 ),
    inference(unit_resulting_resolution,[],[f127,f679,f385])).

fof(f385,plain,
    ( ! [X2] :
        ( v1_funct_1(sK4(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2)))
        | sK4(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2)) = X2
        | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X2) )
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f268,f63])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2))
        | v1_funct_1(X0) )
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f153,f117])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ r2_hidden(X0,k5_partfun1(X1,X2,sK2))
        | v1_funct_1(X0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f67,f102])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f680,plain,
    ( ~ spl8_28
    | spl8_6
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f308,f260,f125,f677])).

fof(f260,plain,
    ( spl8_18
  <=> r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f308,plain,
    ( sK3 != sK4(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | spl8_6
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f127,f262,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f262,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f260])).

fof(f263,plain,
    ( spl8_18
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f224,f213,f198,f120,f115,f105,f100,f260])).

fof(f198,plain,
    ( spl8_9
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f213,plain,
    ( spl8_12
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f224,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f102,f107,f200,f117,f122,f215,f90])).

fof(f90,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(X8,k5_partfun1(X0,X1,X2))
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ( ( ! [X5] :
                    ( ~ r1_partfun1(X2,X5)
                    | ~ v1_partfun1(X5,X0)
                    | sK5(X0,X1,X2,X3) != X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    | ~ v1_funct_1(X5) )
                | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
              & ( ( r1_partfun1(X2,sK6(X0,X1,X2,X3))
                  & v1_partfun1(sK6(X0,X1,X2,X3),X0)
                  & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3)
                  & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(sK6(X0,X1,X2,X3)) )
                | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ( r1_partfun1(X2,sK7(X0,X1,X2,X7))
                    & v1_partfun1(sK7(X0,X1,X2,X7),X0)
                    & sK7(X0,X1,X2,X7) = X7
                    & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(sK7(X0,X1,X2,X7)) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f43,f46,f45,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X2,X5)
                | ~ v1_partfun1(X5,X0)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X2,X6)
                & v1_partfun1(X6,X0)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X2,X5)
              | ~ v1_partfun1(X5,X0)
              | sK5(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK5(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X2,X6)
              & v1_partfun1(X6,X0)
              & sK5(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X6) )
          | r2_hidden(sK5(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X2,X6)
          & v1_partfun1(X6,X0)
          & sK5(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X2,sK6(X0,X1,X2,X3))
        & v1_partfun1(sK6(X0,X1,X2,X3),X0)
        & sK5(X0,X1,X2,X3) = sK6(X0,X1,X2,X3)
        & m1_subset_1(sK6(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK6(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X2,X9)
          & v1_partfun1(X9,X0)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X2,sK7(X0,X1,X2,X7))
        & v1_partfun1(sK7(X0,X1,X2,X7),X0)
        & sK7(X0,X1,X2,X7) = X7
        & m1_subset_1(sK7(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK7(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X6] :
                      ( r1_partfun1(X2,X6)
                      & v1_partfun1(X6,X0)
                      & X4 = X6
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X6) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ? [X9] :
                      ( r1_partfun1(X2,X9)
                      & v1_partfun1(X9,X0)
                      & X7 = X9
                      & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X9) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X3)
                  | ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) ) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f215,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f213])).

fof(f200,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f198])).

fof(f216,plain,
    ( spl8_12
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f170,f120,f115,f105,f100,f213])).

fof(f170,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f107,f102,f117,f122,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(f201,plain,
    ( spl8_9
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f155,f120,f110,f105,f198])).

fof(f155,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f107,f55,f112,f122,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f55,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f128,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f54,f125])).

fof(f54,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f36,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(f123,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f53,f120])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f118,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f50,f115])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f52,f110])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f51,f105])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f103,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f49,f100])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
