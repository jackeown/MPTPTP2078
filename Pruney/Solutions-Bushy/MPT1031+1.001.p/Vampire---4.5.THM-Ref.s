%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1031+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:07 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  155 (1146 expanded)
%              Number of leaves         :   26 ( 387 expanded)
%              Depth                    :   18
%              Number of atoms          :  603 (8110 expanded)
%              Number of equality atoms :   78 (2151 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f109,f124,f178,f184,f279,f311,f462,f502])).

fof(f502,plain,
    ( spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f500,f496])).

fof(f496,plain,
    ( ~ r2_hidden(sK4(sK6(sK1,sK2,sK3)),sK1)
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f480,f479,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | k1_funct_1(sK3,X0) = k1_funct_1(sK6(sK1,sK2,sK3),X0) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | ~ r2_hidden(X0,sK1)
        | k1_funct_1(sK3,X0) = k1_funct_1(sK6(sK1,sK2,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f479,plain,
    ( k1_funct_1(sK6(sK1,sK2,sK3),sK4(sK6(sK1,sK2,sK3))) != k1_funct_1(sK3,sK4(sK6(sK1,sK2,sK3)))
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f475,f476,f477,f52])).

fof(f52,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(X3,sK1,sK2)
      | k1_funct_1(X3,sK4(X3)) != k1_funct_1(sK3,sK4(X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ! [X3] :
        ( ( k1_funct_1(X3,sK4(X3)) != k1_funct_1(sK3,sK4(X3))
          & r2_hidden(sK4(X3),k1_relset_1(sK1,sK2,sK3)) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(X3,sK1,sK2)
        | ~ v1_funct_1(X3) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
                & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X3,X4) != k1_funct_1(sK3,X4)
              & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          | ~ v1_funct_2(X3,sK1,sK2)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) != k1_funct_1(sK3,X4)
          & r2_hidden(X4,k1_relset_1(sK1,sK2,sK3)) )
     => ( k1_funct_1(X3,sK4(X3)) != k1_funct_1(sK3,sK4(X3))
        & r2_hidden(sK4(X3),k1_relset_1(sK1,sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
              & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ~ ( ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ? [X4] :
                    ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
                    & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ? [X4] :
                  ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_funct_2)).

fof(f477,plain,
    ( m1_subset_1(sK6(sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f48,f49,f104,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X4] :
            ( ( ( o_1_1_funct_2(X1) = k1_funct_1(sK6(X0,X1,X2),X4)
                | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              & ( k1_funct_1(X2,X4) = k1_funct_1(sK6(X0,X1,X2),X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6(X0,X1,X2),X0,X1)
        & v1_funct_1(sK6(X0,X1,X2)) )
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X3,X4)
                  | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X3,X4) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ! [X4] :
            ( ( ( o_1_1_funct_2(X1) = k1_funct_1(sK6(X0,X1,X2),X4)
                | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              & ( k1_funct_1(X2,X4) = k1_funct_1(sK6(X0,X1,X2),X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK6(X0,X1,X2),X0,X1)
        & v1_funct_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X3,X4)
                  | r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X3,X4) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X4,X5)
                  | r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X4,X5) = k1_funct_1(X2,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f33,f36])).

fof(f36,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X4,X5)
                  | r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X4,X5) = k1_funct_1(X2,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
      | ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ? [X4] :
          ( ! [X5] :
              ( ( ( o_1_1_funct_2(X1) = k1_funct_1(X4,X5)
                  | r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
                & ( k1_funct_1(X4,X5) = k1_funct_1(X2,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) ) )
              | ~ r2_hidden(X5,X0) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
      | ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ( r2_hidden(X3,X0)
           => ( ( ~ r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(o_1_1_funct_2(X1),X1) )
              & ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(k1_funct_1(X2,X3),X1) ) ) )
       => ? [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
               => ( ( ~ r2_hidden(X5,k1_relset_1(X0,X1,X2))
                   => o_1_1_funct_2(X1) = k1_funct_1(X4,X5) )
                  & ( r2_hidden(X5,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X4,X5) = k1_funct_1(X2,X5) ) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X4,X0,X1)
            & v1_funct_1(X4) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ( r2_hidden(X3,X0)
           => ( ( ~ r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(o_1_1_funct_2(X1),X1) )
              & ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
               => r2_hidden(k1_funct_1(X2,X3),X1) ) ) )
       => ? [X3] :
            ( ! [X4] :
                ( r2_hidden(X4,X0)
               => ( ( ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => o_1_1_funct_2(X1) = k1_funct_1(X3,X4) )
                  & ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X3,X4) = k1_funct_1(X2,X4) ) ) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s5_funct_2__e3_154_1_2__funct_2)).

fof(f104,plain,
    ( ~ sP0(sK2,sK3,sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_3
  <=> sP0(sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f476,plain,
    ( v1_funct_2(sK6(sK1,sK2,sK3),sK1,sK2)
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f48,f49,f104,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK6(X0,X1,X2),X0,X1)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f475,plain,
    ( v1_funct_1(sK6(sK1,sK2,sK3))
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f48,f49,f104,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK6(X0,X1,X2))
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f480,plain,
    ( r2_hidden(sK4(sK6(sK1,sK2,sK3)),k1_relat_1(sK3))
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f475,f476,f477,f93])).

fof(f93,plain,(
    ! [X3] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(X3,sK1,sK2)
      | r2_hidden(sK4(X3),k1_relat_1(sK3)) ) ),
    inference(backward_demodulation,[],[f51,f89])).

fof(f89,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f49,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f51,plain,(
    ! [X3] :
      ( r2_hidden(sK4(X3),k1_relset_1(sK1,sK2,sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_2(X3,sK1,sK2)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f500,plain,
    ( r2_hidden(sK4(sK6(sK1,sK2,sK3)),sK1)
    | spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f463,f490,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f490,plain,
    ( m1_subset_1(sK4(sK6(sK1,sK2,sK3)),sK1)
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f92,f480,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f92,plain,(
    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f90,f89])).

fof(f90,plain,(
    m1_subset_1(k1_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f463,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f84,f77])).

fof(f77,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f53,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f84,plain,
    ( o_0_0_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl7_2
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f462,plain,
    ( ~ spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(trivial_inequality_removal,[],[f458])).

fof(f458,plain,
    ( k1_funct_1(sK3,sK4(sK3)) != k1_funct_1(sK3,sK4(sK3))
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f48,f185,f439,f196])).

fof(f196,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)))
        | ~ v1_funct_2(X3,o_0_0_xboole_0,sK2)
        | k1_funct_1(X3,sK4(X3)) != k1_funct_1(sK3,sK4(X3)) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f186,f85])).

fof(f85,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f186,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,sK1,sK2)
        | k1_funct_1(X3,sK4(X3)) != k1_funct_1(sK3,sK4(X3)) )
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f52,f85])).

fof(f439,plain,
    ( v1_funct_2(sK3,o_0_0_xboole_0,sK2)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f48,f185,f413,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f413,plain,
    ( v1_partfun1(sK3,o_0_0_xboole_0)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f185,f371,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f371,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f350,f365,f57])).

fof(f365,plain,
    ( ~ r2_hidden(sK4(sK6(o_0_0_xboole_0,sK2,sK3)),o_0_0_xboole_0)
    | ~ spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f340,f339,f198])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | ~ r2_hidden(X0,o_0_0_xboole_0)
        | k1_funct_1(sK3,X0) = k1_funct_1(sK6(o_0_0_xboole_0,sK2,sK3),X0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f191,f85])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,o_0_0_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | k1_funct_1(sK3,X0) = k1_funct_1(sK6(sK1,sK2,sK3),X0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f108,f85])).

fof(f339,plain,
    ( k1_funct_1(sK6(o_0_0_xboole_0,sK2,sK3),sK4(sK6(o_0_0_xboole_0,sK2,sK3))) != k1_funct_1(sK3,sK4(sK6(o_0_0_xboole_0,sK2,sK3)))
    | ~ spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f324,f325,f326,f196])).

fof(f326,plain,
    ( m1_subset_1(sK6(o_0_0_xboole_0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)))
    | ~ spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f48,f185,f303,f72])).

fof(f303,plain,
    ( ~ sP0(sK2,sK3,o_0_0_xboole_0)
    | ~ spl7_2
    | spl7_3 ),
    inference(forward_demodulation,[],[f104,f85])).

fof(f325,plain,
    ( v1_funct_2(sK6(o_0_0_xboole_0,sK2,sK3),o_0_0_xboole_0,sK2)
    | ~ spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f48,f185,f303,f71])).

fof(f324,plain,
    ( v1_funct_1(sK6(o_0_0_xboole_0,sK2,sK3))
    | ~ spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f48,f185,f303,f70])).

fof(f340,plain,
    ( r2_hidden(sK4(sK6(o_0_0_xboole_0,sK2,sK3)),k1_relat_1(sK3))
    | ~ spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f324,f325,f326,f197])).

fof(f197,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)))
        | ~ v1_funct_2(X3,o_0_0_xboole_0,sK2)
        | r2_hidden(sK4(X3),k1_relat_1(sK3)) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f189,f85])).

fof(f189,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,sK1,sK2)
        | r2_hidden(sK4(X3),k1_relat_1(sK3)) )
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f93,f85])).

fof(f350,plain,
    ( m1_subset_1(sK4(sK6(o_0_0_xboole_0,sK2,sK3)),o_0_0_xboole_0)
    | ~ spl7_2
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f188,f340,f75])).

fof(f188,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f92,f85])).

fof(f185,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK2)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f49,f85])).

fof(f311,plain,
    ( spl7_13
    | spl7_1 ),
    inference(avatar_split_clause,[],[f310,f79,f181])).

fof(f181,plain,
    ( spl7_13
  <=> r2_hidden(o_1_1_funct_2(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f79,plain,
    ( spl7_1
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f310,plain,
    ( r2_hidden(o_1_1_funct_2(sK2),sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f54,f309,f57])).

fof(f309,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f81,f77])).

fof(f81,plain,
    ( o_0_0_xboole_0 != sK2
    | spl7_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(o_1_1_funct_2(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_1_funct_2)).

fof(f279,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | spl7_13 ),
    inference(trivial_inequality_removal,[],[f275])).

fof(f275,plain,
    ( k1_funct_1(sK3,sK4(sK3)) != k1_funct_1(sK3,sK4(sK3))
    | ~ spl7_1
    | ~ spl7_2
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f48,f201,f248,f211])).

fof(f211,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | ~ v1_funct_2(X3,o_0_0_xboole_0,o_0_0_xboole_0)
        | k1_funct_1(X3,sK4(X3)) != k1_funct_1(sK3,sK4(X3)) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f207,f80])).

fof(f80,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f207,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | ~ v1_funct_2(X3,o_0_0_xboole_0,sK2)
        | ~ v1_funct_1(X3)
        | k1_funct_1(X3,sK4(X3)) != k1_funct_1(sK3,sK4(X3)) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f196,f80])).

fof(f248,plain,
    ( v1_funct_2(sK3,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f48,f201,f236,f63])).

fof(f236,plain,
    ( v1_partfun1(sK3,o_0_0_xboole_0)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f201,f230,f56])).

fof(f230,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_1
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f54,f213,f57])).

fof(f213,plain,
    ( ~ r2_hidden(o_1_1_funct_2(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl7_1
    | spl7_13 ),
    inference(forward_demodulation,[],[f183,f80])).

fof(f183,plain,
    ( ~ r2_hidden(o_1_1_funct_2(sK2),sK2)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f181])).

fof(f201,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f185,f80])).

fof(f184,plain,
    ( ~ spl7_13
    | spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f179,f103,f121,f181])).

fof(f121,plain,
    ( spl7_7
  <=> r2_hidden(sK5(sK2,sK3,sK1),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f179,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),k1_relat_1(sK3))
    | ~ r2_hidden(o_1_1_funct_2(sK2),sK2)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f98,f105])).

fof(f105,plain,
    ( sP0(sK2,sK3,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f98,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),k1_relat_1(sK3))
    | ~ r2_hidden(o_1_1_funct_2(sK2),sK2)
    | ~ sP0(sK2,sK3,sK1) ),
    inference(superposition,[],[f68,f89])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
      | r2_hidden(sK5(X0,X1,X2),k1_relset_1(X2,X0,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
            & ~ r2_hidden(sK5(X0,X1,X2),k1_relset_1(X2,X0,X1)) )
          | ( ~ r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
            & r2_hidden(sK5(X0,X1,X2),k1_relset_1(X2,X0,X1)) ) )
        & r2_hidden(sK5(X0,X1,X2),X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
              & ~ r2_hidden(X3,k1_relset_1(X2,X0,X1)) )
            | ( ~ r2_hidden(k1_funct_1(X1,X3),X0)
              & r2_hidden(X3,k1_relset_1(X2,X0,X1)) ) )
          & r2_hidden(X3,X2) )
     => ( ( ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
            & ~ r2_hidden(sK5(X0,X1,X2),k1_relset_1(X2,X0,X1)) )
          | ( ~ r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
            & r2_hidden(sK5(X0,X1,X2),k1_relset_1(X2,X0,X1)) ) )
        & r2_hidden(sK5(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X0),X0)
              & ~ r2_hidden(X3,k1_relset_1(X2,X0,X1)) )
            | ( ~ r2_hidden(k1_funct_1(X1,X3),X0)
              & r2_hidden(X3,k1_relset_1(X2,X0,X1)) ) )
          & r2_hidden(X3,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(o_1_1_funct_2(X1),X1)
              & ~ r2_hidden(X3,k1_relset_1(X0,X1,X2)) )
            | ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
              & r2_hidden(X3,k1_relset_1(X0,X1,X2)) ) )
          & r2_hidden(X3,X0) )
      | ~ sP0(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f178,plain,
    ( spl7_6
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f175,f119])).

fof(f119,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5(sK2,sK3,sK1)),sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_6
  <=> r2_hidden(k1_funct_1(sK3,sK5(sK2,sK3,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f175,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5(sK2,sK3,sK1)),sK2)
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f88,f91,f48,f122,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_partfun1)).

fof(f122,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),k1_relat_1(sK3))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f91,plain,(
    v5_relat_1(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f49,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f88,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f49,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,
    ( ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f97,f121,f117,f103])).

fof(f97,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),k1_relat_1(sK3))
    | ~ r2_hidden(k1_funct_1(sK3,sK5(sK2,sK3,sK1)),sK2)
    | ~ sP0(sK2,sK3,sK1) ),
    inference(superposition,[],[f67,f89])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),k1_relset_1(X2,X0,X1))
      | ~ r2_hidden(k1_funct_1(X1,sK5(X0,X1,X2)),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f101,f107,f103])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK6(sK1,sK2,sK3),X0)
      | ~ r2_hidden(X0,sK1)
      | sP0(sK2,sK3,sK1) ) ),
    inference(subsumption_resolution,[],[f100,f48])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK6(sK1,sK2,sK3),X0)
      | ~ r2_hidden(X0,sK1)
      | sP0(sK2,sK3,sK1)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | k1_funct_1(sK3,X0) = k1_funct_1(sK6(sK1,sK2,sK3),X0)
      | ~ r2_hidden(X0,sK1)
      | sP0(sK2,sK3,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(sK3) ) ),
    inference(superposition,[],[f73,f89])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_funct_1(X2,X4) = k1_funct_1(sK6(X0,X1,X2),X4)
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | ~ r2_hidden(X4,X0)
      | sP0(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f76,f83,f79])).

fof(f76,plain,
    ( o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f50,f53,f53])).

fof(f50,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f40])).

%------------------------------------------------------------------------------
