%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1011+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:02 EST 2020

% Result     : Theorem 3.47s
% Output     : Refutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 151 expanded)
%              Number of leaves         :   14 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 ( 728 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3379,f3384,f3394,f3404,f3414,f3434,f3439,f4519,f4532])).

fof(f4532,plain,
    ( ~ spl203_1
    | ~ spl203_2
    | ~ spl203_4
    | ~ spl203_6
    | spl203_8
    | ~ spl203_12
    | ~ spl203_13
    | ~ spl203_45 ),
    inference(avatar_contradiction_clause,[],[f4531])).

fof(f4531,plain,
    ( $false
    | ~ spl203_1
    | ~ spl203_2
    | ~ spl203_4
    | ~ spl203_6
    | spl203_8
    | ~ spl203_12
    | ~ spl203_13
    | ~ spl203_45 ),
    inference(subsumption_resolution,[],[f4523,f4530])).

fof(f4530,plain,
    ( sK3 != k1_funct_1(sK4,sK6(sK2,sK4,sK5))
    | ~ spl203_1
    | ~ spl203_2
    | ~ spl203_4
    | ~ spl203_6
    | spl203_8
    | ~ spl203_12
    | ~ spl203_13
    | ~ spl203_45 ),
    inference(backward_demodulation,[],[f3709,f4524])).

fof(f4524,plain,
    ( sK3 = k1_funct_1(sK5,sK6(sK2,sK4,sK5))
    | ~ spl203_2
    | ~ spl203_6
    | ~ spl203_13
    | ~ spl203_45 ),
    inference(unit_resulting_resolution,[],[f3383,f3403,f3438,f4518,f2437])).

fof(f2437,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | k1_funct_1(X3,X2) = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f1604])).

fof(f1604,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f1603])).

fof(f1603,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_2(X3,X0,k1_tarski(X1))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1541])).

fof(f1541,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f4518,plain,
    ( r2_hidden(sK6(sK2,sK4,sK5),sK2)
    | ~ spl203_45 ),
    inference(avatar_component_clause,[],[f4516])).

fof(f4516,plain,
    ( spl203_45
  <=> r2_hidden(sK6(sK2,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl203_45])])).

fof(f3438,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    | ~ spl203_13 ),
    inference(avatar_component_clause,[],[f3436])).

fof(f3436,plain,
    ( spl203_13
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl203_13])])).

fof(f3403,plain,
    ( v1_funct_2(sK5,sK2,k1_tarski(sK3))
    | ~ spl203_6 ),
    inference(avatar_component_clause,[],[f3401])).

fof(f3401,plain,
    ( spl203_6
  <=> v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl203_6])])).

fof(f3383,plain,
    ( v1_funct_1(sK5)
    | ~ spl203_2 ),
    inference(avatar_component_clause,[],[f3381])).

fof(f3381,plain,
    ( spl203_2
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl203_2])])).

fof(f3709,plain,
    ( k1_funct_1(sK4,sK6(sK2,sK4,sK5)) != k1_funct_1(sK5,sK6(sK2,sK4,sK5))
    | ~ spl203_1
    | ~ spl203_2
    | ~ spl203_4
    | ~ spl203_6
    | spl203_8
    | ~ spl203_12
    | ~ spl203_13 ),
    inference(unit_resulting_resolution,[],[f3378,f3383,f3393,f3403,f3413,f3433,f3438,f2382])).

fof(f2382,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3))
      | r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2056])).

fof(f2056,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3))
            & r2_hidden(sK6(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1567,f2055])).

fof(f2055,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK6(X0,X2,X3)) != k1_funct_1(X3,sK6(X0,X2,X3))
        & r2_hidden(sK6(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1567,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1566])).

fof(f1566,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1500])).

fof(f1500,axiom,(
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

fof(f3433,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    | ~ spl203_12 ),
    inference(avatar_component_clause,[],[f3431])).

fof(f3431,plain,
    ( spl203_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl203_12])])).

fof(f3413,plain,
    ( ~ r2_relset_1(sK2,k1_tarski(sK3),sK4,sK5)
    | spl203_8 ),
    inference(avatar_component_clause,[],[f3411])).

fof(f3411,plain,
    ( spl203_8
  <=> r2_relset_1(sK2,k1_tarski(sK3),sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl203_8])])).

fof(f3393,plain,
    ( v1_funct_2(sK4,sK2,k1_tarski(sK3))
    | ~ spl203_4 ),
    inference(avatar_component_clause,[],[f3391])).

fof(f3391,plain,
    ( spl203_4
  <=> v1_funct_2(sK4,sK2,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl203_4])])).

fof(f3378,plain,
    ( v1_funct_1(sK4)
    | ~ spl203_1 ),
    inference(avatar_component_clause,[],[f3376])).

fof(f3376,plain,
    ( spl203_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl203_1])])).

fof(f4523,plain,
    ( sK3 = k1_funct_1(sK4,sK6(sK2,sK4,sK5))
    | ~ spl203_1
    | ~ spl203_4
    | ~ spl203_12
    | ~ spl203_45 ),
    inference(unit_resulting_resolution,[],[f3378,f3393,f3433,f4518,f2437])).

fof(f4519,plain,
    ( spl203_45
    | ~ spl203_1
    | ~ spl203_2
    | ~ spl203_4
    | ~ spl203_6
    | spl203_8
    | ~ spl203_12
    | ~ spl203_13 ),
    inference(avatar_split_clause,[],[f3708,f3436,f3431,f3411,f3401,f3391,f3381,f3376,f4516])).

fof(f3708,plain,
    ( r2_hidden(sK6(sK2,sK4,sK5),sK2)
    | ~ spl203_1
    | ~ spl203_2
    | ~ spl203_4
    | ~ spl203_6
    | spl203_8
    | ~ spl203_12
    | ~ spl203_13 ),
    inference(unit_resulting_resolution,[],[f3378,f3383,f3403,f3393,f3413,f3433,f3438,f2381])).

fof(f2381,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | r2_hidden(sK6(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f2056])).

fof(f3439,plain,(
    spl203_13 ),
    inference(avatar_split_clause,[],[f2375,f3436])).

fof(f2375,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f2053])).

fof(f2053,plain,
    ( ~ r2_relset_1(sK2,k1_tarski(sK3),sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK4,sK2,k1_tarski(sK3))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f1559,f2052,f2051])).

fof(f2051,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK2,k1_tarski(sK3),sK4,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
          & v1_funct_2(X3,sK2,k1_tarski(sK3))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK4,sK2,k1_tarski(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f2052,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK2,k1_tarski(sK3),sK4,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
        & v1_funct_2(X3,sK2,k1_tarski(sK3))
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK2,k1_tarski(sK3),sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f1559,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1558])).

fof(f1558,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1543])).

fof(f1543,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X2,X0,k1_tarski(X1))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    inference(negated_conjecture,[],[f1542])).

fof(f1542,conjecture,(
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

fof(f3434,plain,(
    spl203_12 ),
    inference(avatar_split_clause,[],[f2372,f3431])).

fof(f2372,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f2053])).

fof(f3414,plain,(
    ~ spl203_8 ),
    inference(avatar_split_clause,[],[f2376,f3411])).

fof(f2376,plain,(
    ~ r2_relset_1(sK2,k1_tarski(sK3),sK4,sK5) ),
    inference(cnf_transformation,[],[f2053])).

fof(f3404,plain,(
    spl203_6 ),
    inference(avatar_split_clause,[],[f2374,f3401])).

fof(f2374,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f2053])).

fof(f3394,plain,(
    spl203_4 ),
    inference(avatar_split_clause,[],[f2371,f3391])).

fof(f2371,plain,(
    v1_funct_2(sK4,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f2053])).

fof(f3384,plain,(
    spl203_2 ),
    inference(avatar_split_clause,[],[f2373,f3381])).

fof(f2373,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f2053])).

fof(f3379,plain,(
    spl203_1 ),
    inference(avatar_split_clause,[],[f2370,f3376])).

fof(f2370,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f2053])).
%------------------------------------------------------------------------------
