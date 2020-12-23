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
% DateTime   : Thu Dec  3 13:03:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 342 expanded)
%              Number of leaves         :   31 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          :  807 (2231 expanded)
%              Number of equality atoms :  137 ( 570 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f219,f234,f244,f249,f255,f269,f321,f343,f410])).

fof(f410,plain,
    ( spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_23
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | ~ spl7_29
    | ~ spl7_35
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_23
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | ~ spl7_29
    | ~ spl7_35
    | spl7_39 ),
    inference(subsumption_resolution,[],[f408,f268])).

fof(f268,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl7_29
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f408,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_23
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | ~ spl7_35
    | spl7_39 ),
    inference(forward_demodulation,[],[f407,f218])).

fof(f218,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl7_23
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f407,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | ~ spl7_35
    | spl7_39 ),
    inference(forward_demodulation,[],[f401,f320])).

fof(f320,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl7_35
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f401,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)))
    | spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_28
    | spl7_39 ),
    inference(unit_resulting_resolution,[],[f105,f243,f75,f100,f238,f95,f233,f342,f127])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X2,sK1,X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0
        | r2_relset_1(sK1,X0,X1,X2) )
    | spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f126,f120])).

fof(f120,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X2,sK1,X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0
        | r2_relset_1(sK1,X0,X1,X2)
        | ~ v1_funct_1(sK2) )
    | spl7_2
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f125,f115])).

fof(f115,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X2,sK1,X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0
        | r2_relset_1(sK1,X0,X1,X2)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | spl7_2
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f124,f110])).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X2,sK1,X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0
        | r2_relset_1(sK1,X0,X1,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f123,f70])).

fof(f70,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X2,sK1,X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0
        | r2_relset_1(sK1,X0,X1,X2)
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl7_6 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( sK1 != sK1
        | ~ r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X2,sK1,X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0
        | r2_relset_1(sK1,X0,X1,X2)
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl7_6 ),
    inference(superposition,[],[f45,f90])).

fof(f90,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f45,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ r2_relset_1(X0,X6,k1_partfun1(X0,X1,X1,X6,X2,X7),k1_partfun1(X0,X1,X1,X6,X2,X8))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X6)))
      | ~ v1_funct_2(X8,X1,X6)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X6)))
      | ~ v1_funct_2(X7,X1,X6)
      | ~ v1_funct_1(X7)
      | k1_xboole_0 = X6
      | r2_relset_1(X1,X6,X7,X8)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_relset_1(X0,X1,X2) = X1
          | ( ~ r2_relset_1(X1,sK4(X0,X1,X2),sK5(X0,X1,X2),sK6(X0,X1,X2))
            & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK5(X0,X1,X2)),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK6(X0,X1,X2)))
            & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
            & v1_funct_2(sK6(X0,X1,X2),X1,sK4(X0,X1,X2))
            & v1_funct_1(sK6(X0,X1,X2))
            & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
            & v1_funct_2(sK5(X0,X1,X2),X1,sK4(X0,X1,X2))
            & v1_funct_1(sK5(X0,X1,X2))
            & k1_xboole_0 != sK4(X0,X1,X2) ) )
        & ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( r2_relset_1(X1,X6,X7,X8)
                      | ~ r2_relset_1(X0,X6,k1_partfun1(X0,X1,X1,X6,X2,X7),k1_partfun1(X0,X1,X1,X6,X2,X8))
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X6)))
                      | ~ v1_funct_2(X8,X1,X6)
                      | ~ v1_funct_1(X8) )
                  | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X6)))
                  | ~ v1_funct_2(X7,X1,X6)
                  | ~ v1_funct_1(X7) )
              | k1_xboole_0 = X6 )
          | k2_relset_1(X0,X1,X2) != X1 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_relset_1(X1,X3,X4,X5)
                  & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                  & v1_funct_2(X5,X1,X3)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
              & v1_funct_2(X4,X1,X3)
              & v1_funct_1(X4) )
          & k1_xboole_0 != X3 )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X1,sK4(X0,X1,X2),X4,X5)
                & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X4),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
                & v1_funct_2(X5,X1,sK4(X0,X1,X2))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
            & v1_funct_2(X4,X1,sK4(X0,X1,X2))
            & v1_funct_1(X4) )
        & k1_xboole_0 != sK4(X0,X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_relset_1(X1,sK4(X0,X1,X2),X4,X5)
              & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X4),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
              & v1_funct_2(X5,X1,sK4(X0,X1,X2))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
          & v1_funct_2(X4,X1,sK4(X0,X1,X2))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_relset_1(X1,sK4(X0,X1,X2),sK5(X0,X1,X2),X5)
            & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK5(X0,X1,X2)),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
            & v1_funct_2(X5,X1,sK4(X0,X1,X2))
            & v1_funct_1(X5) )
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
        & v1_funct_2(sK5(X0,X1,X2),X1,sK4(X0,X1,X2))
        & v1_funct_1(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r2_relset_1(X1,sK4(X0,X1,X2),sK5(X0,X1,X2),X5)
          & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK5(X0,X1,X2)),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
          & v1_funct_2(X5,X1,sK4(X0,X1,X2))
          & v1_funct_1(X5) )
     => ( ~ r2_relset_1(X1,sK4(X0,X1,X2),sK5(X0,X1,X2),sK6(X0,X1,X2))
        & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK5(X0,X1,X2)),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK6(X0,X1,X2)))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2))))
        & v1_funct_2(sK6(X0,X1,X2),X1,sK4(X0,X1,X2))
        & v1_funct_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_relset_1(X1,X3,X4,X5)
                      & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                      & v1_funct_2(X5,X1,X3)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                  & v1_funct_2(X4,X1,X3)
                  & v1_funct_1(X4) )
              & k1_xboole_0 != X3 ) )
        & ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( r2_relset_1(X1,X6,X7,X8)
                      | ~ r2_relset_1(X0,X6,k1_partfun1(X0,X1,X1,X6,X2,X7),k1_partfun1(X0,X1,X1,X6,X2,X8))
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X6)))
                      | ~ v1_funct_2(X8,X1,X6)
                      | ~ v1_funct_1(X8) )
                  | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X6)))
                  | ~ v1_funct_2(X7,X1,X6)
                  | ~ v1_funct_1(X7) )
              | k1_xboole_0 = X6 )
          | k2_relset_1(X0,X1,X2) != X1 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_relset_1(X1,X3,X4,X5)
                      & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                      & v1_funct_2(X5,X1,X3)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                  & v1_funct_2(X4,X1,X3)
                  & v1_funct_1(X4) )
              & k1_xboole_0 != X3 ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( r2_relset_1(X1,X3,X4,X5)
                      | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                      | ~ v1_funct_2(X5,X1,X3)
                      | ~ v1_funct_1(X5) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                  | ~ v1_funct_2(X4,X1,X3)
                  | ~ v1_funct_1(X4) )
              | k1_xboole_0 = X3 )
          | k2_relset_1(X0,X1,X2) != X1 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
      <=> ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r2_relset_1(X1,X3,X4,X5)
                    | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    | ~ v1_funct_2(X5,X1,X3)
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                | ~ v1_funct_2(X4,X1,X3)
                | ~ v1_funct_1(X4) )
            | k1_xboole_0 = X3 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
      <=> ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r2_relset_1(X1,X3,X4,X5)
                    | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    | ~ v1_funct_2(X5,X1,X3)
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                | ~ v1_funct_2(X4,X1,X3)
                | ~ v1_funct_1(X4) )
            | k1_xboole_0 = X3 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => ( k2_relset_1(X0,X1,X2) = X1
        <=> ! [X3] :
              ( k1_xboole_0 != X3
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    & v1_funct_2(X4,X1,X3)
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                        & v1_funct_2(X5,X1,X3)
                        & v1_funct_1(X5) )
                     => ( r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                       => r2_relset_1(X1,X3,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_2)).

fof(f342,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2))
    | spl7_39 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl7_39
  <=> r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f233,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl7_26
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f95,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f238,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl7_27
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f100,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f75,plain,
    ( k1_xboole_0 != sK0
    | spl7_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f243,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl7_28
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f105,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f343,plain,
    ( ~ spl7_39
    | spl7_1
    | ~ spl7_7
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f291,f231,f93,f63,f340])).

fof(f63,plain,
    ( spl7_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f291,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f65,f95,f233,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f65,plain,
    ( k2_funct_1(sK2) != sK3
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f321,plain,
    ( spl7_35
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f316,f241,f231,f226,f118,f108,f318])).

fof(f226,plain,
    ( spl7_25
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f316,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f296,f228])).

fof(f228,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f226])).

fof(f296,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_26
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f120,f110,f243,f233,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f269,plain,
    ( spl7_29
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f264,f216,f83,f266])).

fof(f83,plain,
    ( spl7_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f264,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl7_5
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f85,f218])).

fof(f85,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f255,plain,
    ( spl7_25
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f254,f118,f113,f108,f88,f78,f68,f226])).

fof(f78,plain,
    ( spl7_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f254,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f253,f120])).

fof(f253,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f252,f115])).

fof(f252,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f251,f90])).

fof(f251,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_2
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f250,f80])).

fof(f80,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f250,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_2
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f195,f70])).

fof(f195,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f110,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f249,plain,
    ( spl7_27
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f248,f118,f113,f108,f88,f78,f236])).

fof(f248,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f247,f120])).

fof(f247,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f246,f115])).

fof(f246,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f245,f80])).

fof(f245,plain,
    ( ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f192,f90])).

fof(f192,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f110,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f244,plain,
    ( spl7_28
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f182,f118,f113,f108,f88,f78,f241])).

fof(f182,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f120,f80,f115,f90,f110,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f234,plain,
    ( spl7_26
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f184,f118,f113,f108,f88,f78,f231])).

fof(f184,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f120,f80,f115,f90,f110,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f219,plain,
    ( spl7_23
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f187,f118,f108,f103,f93,f216])).

fof(f187,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f120,f105,f95,f110,f59])).

fof(f121,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f30,f118])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f116,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f31,f113])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f32,f108])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f33,f103])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f34,f98])).

fof(f34,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f35,f93])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f36,f88])).

fof(f36,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f40,f68])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f41,f63])).

fof(f41,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:45:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (5645)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (5650)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.49  % (5645)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (5639)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f411,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f219,f234,f244,f249,f255,f269,f321,f343,f410])).
% 0.22/0.50  fof(f410,plain,(
% 0.22/0.50    spl7_2 | spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_23 | ~spl7_26 | ~spl7_27 | ~spl7_28 | ~spl7_29 | ~spl7_35 | spl7_39),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f409])).
% 0.22/0.50  fof(f409,plain,(
% 0.22/0.50    $false | (spl7_2 | spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_23 | ~spl7_26 | ~spl7_27 | ~spl7_28 | ~spl7_29 | ~spl7_35 | spl7_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f408,f268])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~spl7_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f266])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    spl7_29 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | (spl7_2 | spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_23 | ~spl7_26 | ~spl7_27 | ~spl7_28 | ~spl7_35 | spl7_39)),
% 0.22/0.50    inference(forward_demodulation,[],[f407,f218])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~spl7_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f216])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    spl7_23 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.50  fof(f407,plain,(
% 0.22/0.50    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | (spl7_2 | spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_26 | ~spl7_27 | ~spl7_28 | ~spl7_35 | spl7_39)),
% 0.22/0.50    inference(forward_demodulation,[],[f401,f320])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | ~spl7_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f318])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    spl7_35 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.22/0.50  fof(f401,plain,(
% 0.22/0.50    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))) | (spl7_2 | spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_26 | ~spl7_27 | ~spl7_28 | spl7_39)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f105,f243,f75,f100,f238,f95,f233,f342,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X2,sK1,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | r2_relset_1(sK1,X0,X1,X2)) ) | (spl7_2 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f126,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    v1_funct_1(sK2) | ~spl7_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl7_12 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X2,sK1,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | r2_relset_1(sK1,X0,X1,X2) | ~v1_funct_1(sK2)) ) | (spl7_2 | ~spl7_6 | ~spl7_10 | ~spl7_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f125,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    v1_funct_2(sK2,sK0,sK1) | ~spl7_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl7_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X2,sK1,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | r2_relset_1(sK1,X0,X1,X2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (spl7_2 | ~spl7_6 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f124,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl7_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X2,sK1,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | r2_relset_1(sK1,X0,X1,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (spl7_2 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl7_2 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X2,sK1,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | r2_relset_1(sK1,X0,X1,X2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl7_6),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (sK1 != sK1 | ~r2_relset_1(sK0,X0,k1_partfun1(sK0,sK1,sK1,X0,sK2,X1),k1_partfun1(sK0,sK1,sK1,X0,sK2,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X2,sK1,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | r2_relset_1(sK1,X0,X1,X2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl7_6),
% 0.22/0.50    inference(superposition,[],[f45,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl7_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl7_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X6,X2,X0,X8,X7,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~r2_relset_1(X0,X6,k1_partfun1(X0,X1,X1,X6,X2,X7),k1_partfun1(X0,X1,X1,X6,X2,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X6))) | ~v1_funct_2(X8,X1,X6) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X6))) | ~v1_funct_2(X7,X1,X6) | ~v1_funct_1(X7) | k1_xboole_0 = X6 | r2_relset_1(X1,X6,X7,X8) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) = X1 | (((~r2_relset_1(X1,sK4(X0,X1,X2),sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK5(X0,X1,X2)),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK6(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(sK6(X0,X1,X2),X1,sK4(X0,X1,X2)) & v1_funct_1(sK6(X0,X1,X2))) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(sK5(X0,X1,X2),X1,sK4(X0,X1,X2)) & v1_funct_1(sK5(X0,X1,X2))) & k1_xboole_0 != sK4(X0,X1,X2))) & (! [X6] : (! [X7] : (! [X8] : (r2_relset_1(X1,X6,X7,X8) | ~r2_relset_1(X0,X6,k1_partfun1(X0,X1,X1,X6,X2,X7),k1_partfun1(X0,X1,X1,X6,X2,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X6))) | ~v1_funct_2(X8,X1,X6) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X6))) | ~v1_funct_2(X7,X1,X6) | ~v1_funct_1(X7)) | k1_xboole_0 = X6) | k2_relset_1(X0,X1,X2) != X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f24,f27,f26,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X1,X3,X4,X5) & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X5,X1,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X4,X1,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3) => (? [X4] : (? [X5] : (~r2_relset_1(X1,sK4(X0,X1,X2),X4,X5) & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X4),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(X5,X1,sK4(X0,X1,X2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(X4,X1,sK4(X0,X1,X2)) & v1_funct_1(X4)) & k1_xboole_0 != sK4(X0,X1,X2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X4] : (? [X5] : (~r2_relset_1(X1,sK4(X0,X1,X2),X4,X5) & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X4),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(X5,X1,sK4(X0,X1,X2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(X4,X1,sK4(X0,X1,X2)) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(X1,sK4(X0,X1,X2),sK5(X0,X1,X2),X5) & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK5(X0,X1,X2)),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(X5,X1,sK4(X0,X1,X2)) & v1_funct_1(X5)) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(sK5(X0,X1,X2),X1,sK4(X0,X1,X2)) & v1_funct_1(sK5(X0,X1,X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X5] : (~r2_relset_1(X1,sK4(X0,X1,X2),sK5(X0,X1,X2),X5) & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK5(X0,X1,X2)),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(X5,X1,sK4(X0,X1,X2)) & v1_funct_1(X5)) => (~r2_relset_1(X1,sK4(X0,X1,X2),sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_relset_1(X0,sK4(X0,X1,X2),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK5(X0,X1,X2)),k1_partfun1(X0,X1,X1,sK4(X0,X1,X2),X2,sK6(X0,X1,X2))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK4(X0,X1,X2)))) & v1_funct_2(sK6(X0,X1,X2),X1,sK4(X0,X1,X2)) & v1_funct_1(sK6(X0,X1,X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X1,X3,X4,X5) & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X5,X1,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X4,X1,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3)) & (! [X6] : (! [X7] : (! [X8] : (r2_relset_1(X1,X6,X7,X8) | ~r2_relset_1(X0,X6,k1_partfun1(X0,X1,X1,X6,X2,X7),k1_partfun1(X0,X1,X1,X6,X2,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X6))) | ~v1_funct_2(X8,X1,X6) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X1,X6))) | ~v1_funct_2(X7,X1,X6) | ~v1_funct_1(X7)) | k1_xboole_0 = X6) | k2_relset_1(X0,X1,X2) != X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(rectify,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X1,X3,X4,X5) & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X5,X1,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X4,X1,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3)) & (! [X3] : (! [X4] : (! [X5] : (r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4)) | k1_xboole_0 = X3) | k2_relset_1(X0,X1,X2) != X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (! [X4] : (! [X5] : (r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4)) | k1_xboole_0 = X3)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (! [X4] : (! [X5] : ((r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4))) | k1_xboole_0 = X3)) | k1_xboole_0 = X1) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => (k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (k1_xboole_0 != X3 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X4,X1,X3) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X5,X1,X3) & v1_funct_1(X5)) => (r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) => r2_relset_1(X1,X3,X4,X5))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_2)).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    ~r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2)) | spl7_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f340])).
% 0.22/0.50  fof(f340,plain,(
% 0.22/0.50    spl7_39 <=> r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl7_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f231])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    spl7_26 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl7_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl7_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f236])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    spl7_27 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK1,sK0) | ~spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl7_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    k1_xboole_0 != sK0 | spl7_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl7_3 <=> k1_xboole_0 = sK0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    v1_funct_1(k2_funct_1(sK2)) | ~spl7_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f241])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    spl7_28 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl7_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl7_9 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    ~spl7_39 | spl7_1 | ~spl7_7 | ~spl7_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f291,f231,f93,f63,f340])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl7_1 <=> k2_funct_1(sK2) = sK3),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    ~r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2)) | (spl7_1 | ~spl7_7 | ~spl7_26)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f65,f95,f233,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k2_funct_1(sK2) != sK3 | spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    spl7_35 | ~spl7_10 | ~spl7_12 | ~spl7_25 | ~spl7_26 | ~spl7_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f316,f241,f231,f226,f118,f108,f318])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    spl7_25 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.50  fof(f316,plain,(
% 0.22/0.50    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl7_10 | ~spl7_12 | ~spl7_25 | ~spl7_26 | ~spl7_28)),
% 0.22/0.50    inference(forward_demodulation,[],[f296,f228])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl7_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f226])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl7_10 | ~spl7_12 | ~spl7_26 | ~spl7_28)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f120,f110,f243,f233,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    spl7_29 | ~spl7_5 | ~spl7_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f264,f216,f83,f266])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl7_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | (~spl7_5 | ~spl7_23)),
% 0.22/0.50    inference(backward_demodulation,[],[f85,f218])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl7_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f83])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    spl7_25 | spl7_2 | ~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f254,f118,f113,f108,f88,f78,f68,f226])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl7_4 <=> v2_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl7_2 | ~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f253,f120])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl7_2 | ~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f252,f115])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_2 | ~spl7_4 | ~spl7_6 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f251,f90])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    sK1 != k2_relset_1(sK0,sK1,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_2 | ~spl7_4 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f250,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_2 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f195,f70])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl7_10),
% 0.22/0.50    inference(resolution,[],[f110,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    spl7_27 | ~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f248,f118,f113,f108,f88,f78,f236])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f247,f120])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(sK2) | (~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f246,f115])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl7_4 | ~spl7_6 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f245,f80])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl7_6 | ~spl7_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f192,f90])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl7_10),
% 0.22/0.50    inference(resolution,[],[f110,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    spl7_28 | ~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f182,f118,f113,f108,f88,f78,f241])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | (~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f120,f80,f115,f90,f110,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    spl7_26 | ~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f184,f118,f113,f108,f88,f78,f231])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl7_4 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f120,f80,f115,f90,f110,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    spl7_23 | ~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f187,f118,f108,f103,f93,f216])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | (~spl7_7 | ~spl7_9 | ~spl7_10 | ~spl7_12)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f120,f105,f95,f110,f59])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl7_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f118])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f21,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl7_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f31,f113])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f32,f108])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl7_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f33,f103])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl7_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f34,f98])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl7_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f35,f93])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f88])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f37,f83])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl7_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f38,f78])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    v2_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f73])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    k1_xboole_0 != sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ~spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f68])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    k1_xboole_0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ~spl7_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f63])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    k2_funct_1(sK2) != sK3),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (5645)------------------------------
% 0.22/0.51  % (5645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (5645)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (5645)Memory used [KB]: 6652
% 0.22/0.51  % (5645)Time elapsed: 0.074 s
% 0.22/0.51  % (5645)------------------------------
% 0.22/0.51  % (5645)------------------------------
% 0.22/0.51  % (5651)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (5627)Success in time 0.144 s
%------------------------------------------------------------------------------
