%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:55 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 395 expanded)
%              Number of leaves         :   40 ( 175 expanded)
%              Depth                    :   14
%              Number of atoms          :  632 (1731 expanded)
%              Number of equality atoms :  147 ( 467 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1506,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f155,f159,f221,f300,f482,f601,f617,f620,f828,f1077,f1130,f1194,f1399,f1400,f1412,f1425,f1481,f1482,f1483,f1503])).

fof(f1503,plain,
    ( spl8_21
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f1490,f477,f293])).

fof(f293,plain,
    ( spl8_21
  <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f477,plain,
    ( spl8_35
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1490,plain,
    ( r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl8_35 ),
    inference(resolution,[],[f47,f479])).

fof(f479,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f477])).

fof(f47,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f1483,plain,
    ( spl8_6
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f1474,f93,f131])).

fof(f131,plain,
    ( spl8_6
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f93,plain,
    ( spl8_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1474,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_2 ),
    inference(resolution,[],[f95,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f95,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1482,plain,
    ( spl8_7
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f1473,f93,f136])).

fof(f136,plain,
    ( spl8_7
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1473,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_2 ),
    inference(resolution,[],[f95,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

% (2773)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f1481,plain,
    ( spl8_10
    | ~ spl8_2
    | ~ spl8_3
    | spl8_9 ),
    inference(avatar_split_clause,[],[f1480,f147,f98,f93,f151])).

fof(f151,plain,
    ( spl8_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f98,plain,
    ( spl8_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f147,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f1480,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_2
    | ~ spl8_3
    | spl8_9 ),
    inference(subsumption_resolution,[],[f1479,f148])).

fof(f148,plain,
    ( k1_xboole_0 != sK1
    | spl8_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1479,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f1470,f100])).

fof(f100,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f1470,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(resolution,[],[f95,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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

fof(f1425,plain,
    ( spl8_30
    | ~ spl8_31
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f382,f297,f202,f126,f103,f388,f384])).

fof(f384,plain,
    ( spl8_30
  <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f388,plain,
    ( spl8_31
  <=> r2_hidden(sK5(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f103,plain,
    ( spl8_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f126,plain,
    ( spl8_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f202,plain,
    ( spl8_13
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f297,plain,
    ( spl8_22
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f382,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK0)
    | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f381,f204])).

fof(f204,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f202])).

fof(f381,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f380,f128])).

fof(f128,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f380,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f378,f105])).

fof(f105,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f378,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_22 ),
    inference(superposition,[],[f77,f299])).

fof(f299,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f297])).

fof(f77,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

% (2794)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f76,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).

% (2778)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f1412,plain,
    ( k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1400,plain,
    ( ~ spl8_83
    | ~ spl8_4
    | ~ spl8_5
    | spl8_14
    | ~ spl8_23
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f1386,f477,f312,f218,f126,f103,f1396])).

fof(f1396,plain,
    ( spl8_83
  <=> r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f218,plain,
    ( spl8_14
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f312,plain,
    ( spl8_23
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f1386,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_14
    | ~ spl8_23
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f128,f105,f220,f479,f314,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK4(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f314,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f312])).

fof(f220,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f218])).

fof(f1399,plain,
    ( ~ spl8_83
    | spl8_30
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f1392,f312,f126,f103,f384,f1396])).

fof(f1392,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f1391,f128])).

fof(f1391,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f1387,f105])).

fof(f1387,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_23 ),
    inference(superposition,[],[f77,f314])).

fof(f1194,plain,
    ( spl8_23
    | ~ spl8_4
    | ~ spl8_5
    | spl8_14
    | spl8_22 ),
    inference(avatar_split_clause,[],[f1190,f297,f218,f126,f103,f312])).

fof(f1190,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_14
    | spl8_22 ),
    inference(unit_resulting_resolution,[],[f128,f105,f220,f298,f166])).

fof(f166,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | sK1 = k2_relat_1(X3)
      | sK4(X3,sK1) = k1_funct_1(X3,sK5(X3,sK1))
      | sK4(X3,sK1) = k1_funct_1(sK2,sK3(sK4(X3,sK1)))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f48,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f298,plain,
    ( sK4(sK2,sK1) != k1_funct_1(sK2,sK5(sK2,sK1))
    | spl8_22 ),
    inference(avatar_component_clause,[],[f297])).

fof(f1130,plain,
    ( spl8_23
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f1129,f477,f312])).

fof(f1129,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f1116,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f1116,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl8_35 ),
    inference(resolution,[],[f479,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(sK2,sK3(X0)) = X0
      | ~ r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f48,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1077,plain,
    ( ~ spl8_30
    | ~ spl8_12
    | spl8_35 ),
    inference(avatar_split_clause,[],[f1065,f477,f188,f384])).

fof(f188,plain,
    ( spl8_12
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1065,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_12
    | spl8_35 ),
    inference(unit_resulting_resolution,[],[f190,f478,f64])).

fof(f478,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl8_35 ),
    inference(avatar_component_clause,[],[f477])).

fof(f190,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f188])).

fof(f828,plain,
    ( ~ spl8_15
    | ~ spl8_12
    | spl8_14 ),
    inference(avatar_split_clause,[],[f822,f218,f188,f231])).

% (2782)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f231,plain,
    ( spl8_15
  <=> r1_tarski(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f822,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl8_12
    | spl8_14 ),
    inference(unit_resulting_resolution,[],[f190,f220,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f620,plain,
    ( spl8_12
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f618,f141,f126,f188])).

fof(f141,plain,
    ( spl8_8
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f618,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f128,f143,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f143,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f617,plain,
    ( spl8_13
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f200,f151,f131,f202])).

fof(f200,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f133,f153])).

fof(f153,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f133,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f601,plain,
    ( ~ spl8_9
    | spl8_15 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | ~ spl8_9
    | spl8_15 ),
    inference(subsumption_resolution,[],[f552,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f552,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl8_9
    | spl8_15 ),
    inference(backward_demodulation,[],[f233,f149])).

fof(f149,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f233,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f231])).

fof(f482,plain,
    ( spl8_35
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | spl8_14
    | spl8_31 ),
    inference(avatar_split_clause,[],[f481,f388,f218,f202,f126,f103,f477])).

fof(f481,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | spl8_14
    | spl8_31 ),
    inference(subsumption_resolution,[],[f460,f220])).

fof(f460,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_13
    | spl8_31 ),
    inference(resolution,[],[f213,f390])).

fof(f390,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK0)
    | spl8_31 ),
    inference(avatar_component_clause,[],[f388])).

fof(f213,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(sK2,X2),sK0)
        | r2_hidden(sK4(sK2,X2),X2)
        | k2_relat_1(sK2) = X2 )
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f212,f128])).

fof(f212,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(sK2,X2),sK0)
        | k2_relat_1(sK2) = X2
        | r2_hidden(sK4(sK2,X2),X2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_4
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f208,f105])).

fof(f208,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(sK2,X2),sK0)
        | k2_relat_1(sK2) = X2
        | r2_hidden(sK4(sK2,X2),X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_13 ),
    inference(superposition,[],[f55,f204])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f300,plain,
    ( spl8_21
    | spl8_22
    | spl8_14
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f291,f126,f103,f218,f297,f293])).

fof(f291,plain,
    ( sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f290,f128])).

fof(f290,plain,
    ( sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f162,f105])).

fof(f162,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | sK1 = k2_relat_1(X3)
      | sK4(X3,sK1) = k1_funct_1(X3,sK5(X3,sK1))
      | r2_hidden(sK3(sK4(X3,sK1)),sK0)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f47,f56])).

fof(f221,plain,
    ( ~ spl8_14
    | spl8_1
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f216,f136,f88,f218])).

fof(f88,plain,
    ( spl8_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f216,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl8_1
    | ~ spl8_7 ),
    inference(superposition,[],[f90,f138])).

fof(f138,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f90,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f159,plain,
    ( spl8_5
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f158,f93,f126])).

fof(f158,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f124,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f124,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_2 ),
    inference(resolution,[],[f95,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f155,plain,
    ( spl8_8
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f121,f93,f141])).

fof(f121,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl8_2 ),
    inference(resolution,[],[f95,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f106,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f44,f103])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

% (2799)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f101,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f45,f98])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f46,f93])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (2783)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (2798)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.48  % (2783)Refutation not found, incomplete strategy% (2783)------------------------------
% 0.21/0.48  % (2783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2783)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2783)Memory used [KB]: 10746
% 0.21/0.48  % (2783)Time elapsed: 0.074 s
% 0.21/0.48  % (2783)------------------------------
% 0.21/0.48  % (2783)------------------------------
% 1.20/0.51  % (2777)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.52  % (2780)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.52  % (2790)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.20/0.52  % (2802)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.20/0.52  % (2790)Refutation not found, incomplete strategy% (2790)------------------------------
% 1.20/0.52  % (2790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (2790)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (2790)Memory used [KB]: 10746
% 1.20/0.52  % (2790)Time elapsed: 0.117 s
% 1.20/0.52  % (2790)------------------------------
% 1.20/0.52  % (2790)------------------------------
% 1.20/0.53  % (2776)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.53  % (2798)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f1506,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f155,f159,f221,f300,f482,f601,f617,f620,f828,f1077,f1130,f1194,f1399,f1400,f1412,f1425,f1481,f1482,f1483,f1503])).
% 1.34/0.53  fof(f1503,plain,(
% 1.34/0.53    spl8_21 | ~spl8_35),
% 1.34/0.53    inference(avatar_split_clause,[],[f1490,f477,f293])).
% 1.34/0.53  fof(f293,plain,(
% 1.34/0.53    spl8_21 <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.34/0.53  fof(f477,plain,(
% 1.34/0.53    spl8_35 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 1.34/0.53  fof(f1490,plain,(
% 1.34/0.53    r2_hidden(sK3(sK4(sK2,sK1)),sK0) | ~spl8_35),
% 1.34/0.53    inference(resolution,[],[f47,f479])).
% 1.34/0.53  fof(f479,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),sK1) | ~spl8_35),
% 1.34/0.53    inference(avatar_component_clause,[],[f477])).
% 1.34/0.53  fof(f47,plain,(
% 1.34/0.53    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f28,f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.34/0.53    inference(flattening,[],[f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.34/0.53    inference(ennf_transformation,[],[f13])).
% 1.34/0.53  fof(f13,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.34/0.53    inference(negated_conjecture,[],[f12])).
% 1.34/0.53  fof(f12,conjecture,(
% 1.34/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 1.34/0.53  fof(f1483,plain,(
% 1.34/0.53    spl8_6 | ~spl8_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f1474,f93,f131])).
% 1.34/0.53  fof(f131,plain,(
% 1.34/0.53    spl8_6 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.34/0.53  fof(f93,plain,(
% 1.34/0.53    spl8_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.34/0.53  fof(f1474,plain,(
% 1.34/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl8_2),
% 1.34/0.53    inference(resolution,[],[f95,f67])).
% 1.34/0.53  fof(f67,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f22])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.34/0.53  fof(f95,plain,(
% 1.34/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f93])).
% 1.34/0.53  fof(f1482,plain,(
% 1.34/0.53    spl8_7 | ~spl8_2),
% 1.34/0.53    inference(avatar_split_clause,[],[f1473,f93,f136])).
% 1.34/0.53  fof(f136,plain,(
% 1.34/0.53    spl8_7 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.34/0.53  fof(f1473,plain,(
% 1.34/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_2),
% 1.34/0.53    inference(resolution,[],[f95,f68])).
% 1.34/0.53  fof(f68,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f23])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.34/0.53  % (2773)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.53  fof(f1481,plain,(
% 1.34/0.53    spl8_10 | ~spl8_2 | ~spl8_3 | spl8_9),
% 1.34/0.53    inference(avatar_split_clause,[],[f1480,f147,f98,f93,f151])).
% 1.34/0.53  fof(f151,plain,(
% 1.34/0.53    spl8_10 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.34/0.53  fof(f98,plain,(
% 1.34/0.53    spl8_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.34/0.53  fof(f147,plain,(
% 1.34/0.53    spl8_9 <=> k1_xboole_0 = sK1),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.34/0.53  fof(f1480,plain,(
% 1.34/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl8_2 | ~spl8_3 | spl8_9)),
% 1.34/0.53    inference(subsumption_resolution,[],[f1479,f148])).
% 1.34/0.53  fof(f148,plain,(
% 1.34/0.53    k1_xboole_0 != sK1 | spl8_9),
% 1.34/0.53    inference(avatar_component_clause,[],[f147])).
% 1.34/0.53  fof(f1479,plain,(
% 1.34/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | (~spl8_2 | ~spl8_3)),
% 1.34/0.53    inference(subsumption_resolution,[],[f1470,f100])).
% 1.34/0.53  fof(f100,plain,(
% 1.34/0.53    v1_funct_2(sK2,sK0,sK1) | ~spl8_3),
% 1.34/0.53    inference(avatar_component_clause,[],[f98])).
% 1.34/0.53  fof(f1470,plain,(
% 1.34/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~spl8_2),
% 1.34/0.53    inference(resolution,[],[f95,f70])).
% 1.34/0.53  fof(f70,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f43])).
% 1.34/0.53  fof(f43,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(nnf_transformation,[],[f26])).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(flattening,[],[f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.34/0.53  fof(f1425,plain,(
% 1.34/0.53    spl8_30 | ~spl8_31 | ~spl8_4 | ~spl8_5 | ~spl8_13 | ~spl8_22),
% 1.34/0.53    inference(avatar_split_clause,[],[f382,f297,f202,f126,f103,f388,f384])).
% 1.34/0.53  fof(f384,plain,(
% 1.34/0.53    spl8_30 <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 1.34/0.53  fof(f388,plain,(
% 1.34/0.53    spl8_31 <=> r2_hidden(sK5(sK2,sK1),sK0)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 1.34/0.53  fof(f103,plain,(
% 1.34/0.53    spl8_4 <=> v1_funct_1(sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.34/0.53  fof(f126,plain,(
% 1.34/0.53    spl8_5 <=> v1_relat_1(sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.34/0.53  fof(f202,plain,(
% 1.34/0.53    spl8_13 <=> sK0 = k1_relat_1(sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.34/0.53  fof(f297,plain,(
% 1.34/0.53    spl8_22 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.34/0.53  fof(f382,plain,(
% 1.34/0.53    ~r2_hidden(sK5(sK2,sK1),sK0) | r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | (~spl8_4 | ~spl8_5 | ~spl8_13 | ~spl8_22)),
% 1.34/0.53    inference(forward_demodulation,[],[f381,f204])).
% 1.34/0.53  fof(f204,plain,(
% 1.34/0.53    sK0 = k1_relat_1(sK2) | ~spl8_13),
% 1.34/0.53    inference(avatar_component_clause,[],[f202])).
% 1.34/0.53  fof(f381,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | (~spl8_4 | ~spl8_5 | ~spl8_22)),
% 1.34/0.53    inference(subsumption_resolution,[],[f380,f128])).
% 1.34/0.53  fof(f128,plain,(
% 1.34/0.53    v1_relat_1(sK2) | ~spl8_5),
% 1.34/0.53    inference(avatar_component_clause,[],[f126])).
% 1.34/0.53  fof(f380,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl8_4 | ~spl8_22)),
% 1.34/0.53    inference(subsumption_resolution,[],[f378,f105])).
% 1.34/0.53  fof(f105,plain,(
% 1.34/0.53    v1_funct_1(sK2) | ~spl8_4),
% 1.34/0.53    inference(avatar_component_clause,[],[f103])).
% 1.34/0.53  fof(f378,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_22),
% 1.34/0.53    inference(superposition,[],[f77,f299])).
% 1.34/0.53  fof(f299,plain,(
% 1.34/0.53    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | ~spl8_22),
% 1.34/0.53    inference(avatar_component_clause,[],[f297])).
% 1.34/0.53  fof(f77,plain,(
% 1.34/0.53    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.53    inference(equality_resolution,[],[f76])).
% 1.34/0.53  % (2794)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.53  fof(f76,plain,(
% 1.34/0.53    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.53    inference(equality_resolution,[],[f54])).
% 1.34/0.53  fof(f54,plain,(
% 1.34/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f35])).
% 1.34/0.53  fof(f35,plain,(
% 1.34/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).
% 1.34/0.53  % (2778)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.53    inference(rectify,[],[f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.53    inference(nnf_transformation,[],[f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.53    inference(flattening,[],[f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.53    inference(ennf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,axiom,(
% 1.34/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.34/0.53  fof(f1412,plain,(
% 1.34/0.53    k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | sK0 != k1_relset_1(sK0,sK1,sK2) | r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 1.34/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.34/0.53  fof(f1400,plain,(
% 1.34/0.53    ~spl8_83 | ~spl8_4 | ~spl8_5 | spl8_14 | ~spl8_23 | ~spl8_35),
% 1.34/0.53    inference(avatar_split_clause,[],[f1386,f477,f312,f218,f126,f103,f1396])).
% 1.34/0.53  fof(f1396,plain,(
% 1.34/0.53    spl8_83 <=> r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).
% 1.34/0.53  fof(f218,plain,(
% 1.34/0.53    spl8_14 <=> sK1 = k2_relat_1(sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.34/0.53  fof(f312,plain,(
% 1.34/0.53    spl8_23 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.34/0.53  fof(f1386,plain,(
% 1.34/0.53    ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | (~spl8_4 | ~spl8_5 | spl8_14 | ~spl8_23 | ~spl8_35)),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f128,f105,f220,f479,f314,f57])).
% 1.34/0.53  fof(f57,plain,(
% 1.34/0.53    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f35])).
% 1.34/0.53  fof(f314,plain,(
% 1.34/0.53    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_23),
% 1.34/0.53    inference(avatar_component_clause,[],[f312])).
% 1.34/0.53  fof(f220,plain,(
% 1.34/0.53    sK1 != k2_relat_1(sK2) | spl8_14),
% 1.34/0.53    inference(avatar_component_clause,[],[f218])).
% 1.34/0.53  fof(f1399,plain,(
% 1.34/0.53    ~spl8_83 | spl8_30 | ~spl8_4 | ~spl8_5 | ~spl8_23),
% 1.34/0.53    inference(avatar_split_clause,[],[f1392,f312,f126,f103,f384,f1396])).
% 1.34/0.53  fof(f1392,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | (~spl8_4 | ~spl8_5 | ~spl8_23)),
% 1.34/0.53    inference(subsumption_resolution,[],[f1391,f128])).
% 1.34/0.53  fof(f1391,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl8_4 | ~spl8_23)),
% 1.34/0.53    inference(subsumption_resolution,[],[f1387,f105])).
% 1.34/0.53  fof(f1387,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_23),
% 1.34/0.53    inference(superposition,[],[f77,f314])).
% 1.34/0.53  fof(f1194,plain,(
% 1.34/0.53    spl8_23 | ~spl8_4 | ~spl8_5 | spl8_14 | spl8_22),
% 1.34/0.53    inference(avatar_split_clause,[],[f1190,f297,f218,f126,f103,f312])).
% 1.34/0.53  fof(f1190,plain,(
% 1.34/0.53    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl8_4 | ~spl8_5 | spl8_14 | spl8_22)),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f128,f105,f220,f298,f166])).
% 1.34/0.53  fof(f166,plain,(
% 1.34/0.53    ( ! [X3] : (~v1_funct_1(X3) | sK1 = k2_relat_1(X3) | sK4(X3,sK1) = k1_funct_1(X3,sK5(X3,sK1)) | sK4(X3,sK1) = k1_funct_1(sK2,sK3(sK4(X3,sK1))) | ~v1_relat_1(X3)) )),
% 1.34/0.53    inference(resolution,[],[f48,f56])).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f35])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 1.34/0.53    inference(cnf_transformation,[],[f29])).
% 1.34/0.53  fof(f298,plain,(
% 1.34/0.53    sK4(sK2,sK1) != k1_funct_1(sK2,sK5(sK2,sK1)) | spl8_22),
% 1.34/0.53    inference(avatar_component_clause,[],[f297])).
% 1.34/0.53  fof(f1130,plain,(
% 1.34/0.53    spl8_23 | ~spl8_35),
% 1.34/0.53    inference(avatar_split_clause,[],[f1129,f477,f312])).
% 1.34/0.53  fof(f1129,plain,(
% 1.34/0.53    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_35),
% 1.34/0.53    inference(subsumption_resolution,[],[f1116,f81])).
% 1.34/0.53  fof(f81,plain,(
% 1.34/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.53    inference(equality_resolution,[],[f61])).
% 1.34/0.53  fof(f61,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f38])).
% 1.34/0.53  fof(f38,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(flattening,[],[f37])).
% 1.34/0.53  fof(f37,plain,(
% 1.34/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.53    inference(nnf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.53  fof(f1116,plain,(
% 1.34/0.53    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~r1_tarski(sK1,sK1) | ~spl8_35),
% 1.34/0.53    inference(resolution,[],[f479,f164])).
% 1.34/0.53  fof(f164,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(sK2,sK3(X0)) = X0 | ~r1_tarski(X1,sK1)) )),
% 1.34/0.53    inference(resolution,[],[f48,f64])).
% 1.34/0.53  fof(f64,plain,(
% 1.34/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f42])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 1.34/0.53  fof(f41,plain,(
% 1.34/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f40,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.53    inference(rectify,[],[f39])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.34/0.53    inference(nnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.34/0.53    inference(ennf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.34/0.53  fof(f1077,plain,(
% 1.34/0.53    ~spl8_30 | ~spl8_12 | spl8_35),
% 1.34/0.53    inference(avatar_split_clause,[],[f1065,f477,f188,f384])).
% 1.34/0.53  fof(f188,plain,(
% 1.34/0.53    spl8_12 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.34/0.53  fof(f1065,plain,(
% 1.34/0.53    ~r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | (~spl8_12 | spl8_35)),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f190,f478,f64])).
% 1.34/0.53  fof(f478,plain,(
% 1.34/0.53    ~r2_hidden(sK4(sK2,sK1),sK1) | spl8_35),
% 1.34/0.53    inference(avatar_component_clause,[],[f477])).
% 1.34/0.53  fof(f190,plain,(
% 1.34/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~spl8_12),
% 1.34/0.53    inference(avatar_component_clause,[],[f188])).
% 1.34/0.53  fof(f828,plain,(
% 1.34/0.53    ~spl8_15 | ~spl8_12 | spl8_14),
% 1.34/0.53    inference(avatar_split_clause,[],[f822,f218,f188,f231])).
% 1.34/0.53  % (2782)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.53  fof(f231,plain,(
% 1.34/0.53    spl8_15 <=> r1_tarski(sK1,k2_relat_1(sK2))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.34/0.53  fof(f822,plain,(
% 1.34/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | (~spl8_12 | spl8_14)),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f190,f220,f63])).
% 1.34/0.53  fof(f63,plain,(
% 1.34/0.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f38])).
% 1.34/0.53  fof(f620,plain,(
% 1.34/0.53    spl8_12 | ~spl8_5 | ~spl8_8),
% 1.34/0.53    inference(avatar_split_clause,[],[f618,f141,f126,f188])).
% 1.34/0.53  fof(f141,plain,(
% 1.34/0.53    spl8_8 <=> v5_relat_1(sK2,sK1)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.34/0.53  fof(f618,plain,(
% 1.34/0.53    r1_tarski(k2_relat_1(sK2),sK1) | (~spl8_5 | ~spl8_8)),
% 1.34/0.53    inference(unit_resulting_resolution,[],[f128,f143,f59])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f36])).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(nnf_transformation,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(ennf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.34/0.53  fof(f143,plain,(
% 1.34/0.53    v5_relat_1(sK2,sK1) | ~spl8_8),
% 1.34/0.53    inference(avatar_component_clause,[],[f141])).
% 1.34/0.53  fof(f617,plain,(
% 1.34/0.53    spl8_13 | ~spl8_6 | ~spl8_10),
% 1.34/0.53    inference(avatar_split_clause,[],[f200,f151,f131,f202])).
% 1.34/0.53  fof(f200,plain,(
% 1.34/0.53    sK0 = k1_relat_1(sK2) | (~spl8_6 | ~spl8_10)),
% 1.34/0.53    inference(forward_demodulation,[],[f133,f153])).
% 1.34/0.53  fof(f153,plain,(
% 1.34/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_10),
% 1.34/0.53    inference(avatar_component_clause,[],[f151])).
% 1.34/0.53  fof(f133,plain,(
% 1.34/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl8_6),
% 1.34/0.53    inference(avatar_component_clause,[],[f131])).
% 1.34/0.53  fof(f601,plain,(
% 1.34/0.53    ~spl8_9 | spl8_15),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f600])).
% 1.34/0.53  fof(f600,plain,(
% 1.34/0.53    $false | (~spl8_9 | spl8_15)),
% 1.34/0.53    inference(subsumption_resolution,[],[f552,f50])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.34/0.53  fof(f552,plain,(
% 1.34/0.53    ~r1_tarski(k1_xboole_0,k2_relat_1(sK2)) | (~spl8_9 | spl8_15)),
% 1.34/0.53    inference(backward_demodulation,[],[f233,f149])).
% 1.34/0.53  fof(f149,plain,(
% 1.34/0.53    k1_xboole_0 = sK1 | ~spl8_9),
% 1.34/0.53    inference(avatar_component_clause,[],[f147])).
% 1.34/0.53  fof(f233,plain,(
% 1.34/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl8_15),
% 1.34/0.53    inference(avatar_component_clause,[],[f231])).
% 1.34/0.53  fof(f482,plain,(
% 1.34/0.53    spl8_35 | ~spl8_4 | ~spl8_5 | ~spl8_13 | spl8_14 | spl8_31),
% 1.34/0.53    inference(avatar_split_clause,[],[f481,f388,f218,f202,f126,f103,f477])).
% 1.34/0.53  fof(f481,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_4 | ~spl8_5 | ~spl8_13 | spl8_14 | spl8_31)),
% 1.34/0.53    inference(subsumption_resolution,[],[f460,f220])).
% 1.34/0.53  fof(f460,plain,(
% 1.34/0.53    r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | (~spl8_4 | ~spl8_5 | ~spl8_13 | spl8_31)),
% 1.34/0.53    inference(resolution,[],[f213,f390])).
% 1.34/0.53  fof(f390,plain,(
% 1.34/0.53    ~r2_hidden(sK5(sK2,sK1),sK0) | spl8_31),
% 1.34/0.53    inference(avatar_component_clause,[],[f388])).
% 1.34/0.53  fof(f213,plain,(
% 1.34/0.53    ( ! [X2] : (r2_hidden(sK5(sK2,X2),sK0) | r2_hidden(sK4(sK2,X2),X2) | k2_relat_1(sK2) = X2) ) | (~spl8_4 | ~spl8_5 | ~spl8_13)),
% 1.34/0.53    inference(subsumption_resolution,[],[f212,f128])).
% 1.34/0.53  fof(f212,plain,(
% 1.34/0.53    ( ! [X2] : (r2_hidden(sK5(sK2,X2),sK0) | k2_relat_1(sK2) = X2 | r2_hidden(sK4(sK2,X2),X2) | ~v1_relat_1(sK2)) ) | (~spl8_4 | ~spl8_13)),
% 1.34/0.53    inference(subsumption_resolution,[],[f208,f105])).
% 1.34/0.53  fof(f208,plain,(
% 1.34/0.53    ( ! [X2] : (r2_hidden(sK5(sK2,X2),sK0) | k2_relat_1(sK2) = X2 | r2_hidden(sK4(sK2,X2),X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_13),
% 1.34/0.53    inference(superposition,[],[f55,f204])).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f35])).
% 1.34/0.53  fof(f300,plain,(
% 1.34/0.53    spl8_21 | spl8_22 | spl8_14 | ~spl8_4 | ~spl8_5),
% 1.34/0.53    inference(avatar_split_clause,[],[f291,f126,f103,f218,f297,f293])).
% 1.34/0.53  fof(f291,plain,(
% 1.34/0.53    sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | r2_hidden(sK3(sK4(sK2,sK1)),sK0) | (~spl8_4 | ~spl8_5)),
% 1.34/0.53    inference(subsumption_resolution,[],[f290,f128])).
% 1.34/0.53  fof(f290,plain,(
% 1.34/0.53    sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | r2_hidden(sK3(sK4(sK2,sK1)),sK0) | ~v1_relat_1(sK2) | ~spl8_4),
% 1.34/0.53    inference(resolution,[],[f162,f105])).
% 1.34/0.53  fof(f162,plain,(
% 1.34/0.53    ( ! [X3] : (~v1_funct_1(X3) | sK1 = k2_relat_1(X3) | sK4(X3,sK1) = k1_funct_1(X3,sK5(X3,sK1)) | r2_hidden(sK3(sK4(X3,sK1)),sK0) | ~v1_relat_1(X3)) )),
% 1.34/0.53    inference(resolution,[],[f47,f56])).
% 1.34/0.53  fof(f221,plain,(
% 1.34/0.53    ~spl8_14 | spl8_1 | ~spl8_7),
% 1.34/0.53    inference(avatar_split_clause,[],[f216,f136,f88,f218])).
% 1.34/0.53  fof(f88,plain,(
% 1.34/0.53    spl8_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.34/0.53  fof(f216,plain,(
% 1.34/0.53    sK1 != k2_relat_1(sK2) | (spl8_1 | ~spl8_7)),
% 1.34/0.53    inference(superposition,[],[f90,f138])).
% 1.34/0.53  fof(f138,plain,(
% 1.34/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl8_7),
% 1.34/0.53    inference(avatar_component_clause,[],[f136])).
% 1.34/0.54  fof(f90,plain,(
% 1.34/0.54    sK1 != k2_relset_1(sK0,sK1,sK2) | spl8_1),
% 1.34/0.54    inference(avatar_component_clause,[],[f88])).
% 1.34/0.54  fof(f159,plain,(
% 1.34/0.54    spl8_5 | ~spl8_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f158,f93,f126])).
% 1.34/0.54  fof(f158,plain,(
% 1.34/0.54    v1_relat_1(sK2) | ~spl8_2),
% 1.34/0.54    inference(subsumption_resolution,[],[f124,f58])).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.54  fof(f124,plain,(
% 1.34/0.54    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl8_2),
% 1.34/0.54    inference(resolution,[],[f95,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.54  fof(f155,plain,(
% 1.34/0.54    spl8_8 | ~spl8_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f121,f93,f141])).
% 1.34/0.54  fof(f121,plain,(
% 1.34/0.54    v5_relat_1(sK2,sK1) | ~spl8_2),
% 1.34/0.54    inference(resolution,[],[f95,f69])).
% 1.34/0.54  fof(f69,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.54    inference(ennf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.34/0.54    inference(pure_predicate_removal,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.54  fof(f106,plain,(
% 1.34/0.54    spl8_4),
% 1.34/0.54    inference(avatar_split_clause,[],[f44,f103])).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    v1_funct_1(sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  % (2799)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  fof(f101,plain,(
% 1.34/0.54    spl8_3),
% 1.34/0.54    inference(avatar_split_clause,[],[f45,f98])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    v1_funct_2(sK2,sK0,sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  fof(f96,plain,(
% 1.34/0.54    spl8_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f46,f93])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  fof(f91,plain,(
% 1.34/0.54    ~spl8_1),
% 1.34/0.54    inference(avatar_split_clause,[],[f49,f88])).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.34/0.54    inference(cnf_transformation,[],[f29])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (2798)------------------------------
% 1.34/0.54  % (2798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (2775)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.54  % (2798)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (2798)Memory used [KB]: 7036
% 1.34/0.54  % (2798)Time elapsed: 0.121 s
% 1.34/0.54  % (2798)------------------------------
% 1.34/0.54  % (2798)------------------------------
% 1.34/0.54  % (2792)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  % (2772)Success in time 0.18 s
%------------------------------------------------------------------------------
