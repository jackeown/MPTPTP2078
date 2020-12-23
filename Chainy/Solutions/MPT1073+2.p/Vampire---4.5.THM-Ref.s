%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1073+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 7.26s
% Output     : Refutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 106 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 ( 418 expanded)
%              Number of equality atoms :   22 (  57 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13926,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3903,f3908,f3913,f3918,f4387,f4600,f12415,f13907])).

fof(f13907,plain,
    ( ~ spl280_45
    | ~ spl280_428 ),
    inference(avatar_contradiction_clause,[],[f13906])).

fof(f13906,plain,
    ( $false
    | ~ spl280_45
    | ~ spl280_428 ),
    inference(subsumption_resolution,[],[f13903,f12414])).

fof(f12414,plain,
    ( m1_subset_1(sK38(sK1,sK0,sK3),sK1)
    | ~ spl280_428 ),
    inference(avatar_component_clause,[],[f12412])).

fof(f12412,plain,
    ( spl280_428
  <=> m1_subset_1(sK38(sK1,sK0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_428])])).

fof(f13903,plain,
    ( ~ m1_subset_1(sK38(sK1,sK0,sK3),sK1)
    | ~ spl280_45 ),
    inference(trivial_inequality_removal,[],[f13889])).

fof(f13889,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK38(sK1,sK0,sK3),sK1)
    | ~ spl280_45 ),
    inference(superposition,[],[f2519,f4386])).

fof(f4386,plain,
    ( sK0 = k1_funct_1(sK3,sK38(sK1,sK0,sK3))
    | ~ spl280_45 ),
    inference(avatar_component_clause,[],[f4384])).

fof(f4384,plain,
    ( spl280_45
  <=> sK0 = k1_funct_1(sK3,sK38(sK1,sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_45])])).

fof(f2519,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f2194])).

fof(f2194,plain,
    ( ! [X4] :
        ( sK0 != k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK1) )
    & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1691,f2193])).

fof(f2193,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK0 != k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK1) )
      & r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1691,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1690])).

fof(f1690,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1619])).

fof(f1619,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f1618])).

fof(f1618,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f12415,plain,
    ( spl280_428
    | ~ spl280_66 ),
    inference(avatar_split_clause,[],[f11973,f4597,f12412])).

fof(f4597,plain,
    ( spl280_66
  <=> r2_hidden(sK38(sK1,sK0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_66])])).

fof(f11973,plain,
    ( m1_subset_1(sK38(sK1,sK0,sK3),sK1)
    | ~ spl280_66 ),
    inference(unit_resulting_resolution,[],[f4599,f2794])).

fof(f2794,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1753])).

fof(f1753,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f4599,plain,
    ( r2_hidden(sK38(sK1,sK0,sK3),sK1)
    | ~ spl280_66 ),
    inference(avatar_component_clause,[],[f4597])).

fof(f4600,plain,
    ( spl280_66
    | ~ spl280_1
    | ~ spl280_2
    | ~ spl280_3
    | ~ spl280_4 ),
    inference(avatar_split_clause,[],[f4463,f3915,f3910,f3905,f3900,f4597])).

fof(f3900,plain,
    ( spl280_1
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_1])])).

fof(f3905,plain,
    ( spl280_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_2])])).

fof(f3910,plain,
    ( spl280_3
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_3])])).

fof(f3915,plain,
    ( spl280_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl280_4])])).

fof(f4463,plain,
    ( r2_hidden(sK38(sK1,sK0,sK3),sK1)
    | ~ spl280_1
    | ~ spl280_2
    | ~ spl280_3
    | ~ spl280_4 ),
    inference(unit_resulting_resolution,[],[f3917,f3912,f3902,f3907,f2796])).

fof(f2796,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK38(X0,X2,X3),X0)
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f2265])).

fof(f2265,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_funct_1(X3,sK38(X0,X2,X3)) = X2
        & r2_hidden(sK38(X0,X2,X3),X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK38])],[f1756,f2264])).

fof(f2264,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X3,sK38(X0,X2,X3)) = X2
        & r2_hidden(sK38(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1756,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f1755])).

fof(f1755,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) = X2
          & r2_hidden(X4,X0) )
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1606])).

fof(f1606,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(f3907,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl280_2 ),
    inference(avatar_component_clause,[],[f3905])).

fof(f3902,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl280_1 ),
    inference(avatar_component_clause,[],[f3900])).

fof(f3912,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl280_3 ),
    inference(avatar_component_clause,[],[f3910])).

fof(f3917,plain,
    ( v1_funct_1(sK3)
    | ~ spl280_4 ),
    inference(avatar_component_clause,[],[f3915])).

fof(f4387,plain,
    ( spl280_45
    | ~ spl280_1
    | ~ spl280_2
    | ~ spl280_3
    | ~ spl280_4 ),
    inference(avatar_split_clause,[],[f4382,f3915,f3910,f3905,f3900,f4384])).

fof(f4382,plain,
    ( sK0 = k1_funct_1(sK3,sK38(sK1,sK0,sK3))
    | ~ spl280_1
    | ~ spl280_2
    | ~ spl280_3
    | ~ spl280_4 ),
    inference(subsumption_resolution,[],[f4381,f3917])).

fof(f4381,plain,
    ( sK0 = k1_funct_1(sK3,sK38(sK1,sK0,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl280_1
    | ~ spl280_2
    | ~ spl280_3 ),
    inference(subsumption_resolution,[],[f4380,f3912])).

fof(f4380,plain,
    ( sK0 = k1_funct_1(sK3,sK38(sK1,sK0,sK3))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl280_1
    | ~ spl280_2 ),
    inference(subsumption_resolution,[],[f4109,f3907])).

fof(f4109,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK0 = k1_funct_1(sK3,sK38(sK1,sK0,sK3))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl280_1 ),
    inference(resolution,[],[f3902,f2797])).

fof(f2797,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k2_relset_1(X0,X1,X3))
      | k1_funct_1(X3,sK38(X0,X2,X3)) = X2
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f2265])).

fof(f3918,plain,(
    spl280_4 ),
    inference(avatar_split_clause,[],[f2515,f3915])).

fof(f2515,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f2194])).

fof(f3913,plain,(
    spl280_3 ),
    inference(avatar_split_clause,[],[f2516,f3910])).

fof(f2516,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f2194])).

fof(f3908,plain,(
    spl280_2 ),
    inference(avatar_split_clause,[],[f2517,f3905])).

fof(f2517,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f2194])).

fof(f3903,plain,(
    spl280_1 ),
    inference(avatar_split_clause,[],[f2518,f3900])).

fof(f2518,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f2194])).
%------------------------------------------------------------------------------
