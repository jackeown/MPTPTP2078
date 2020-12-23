%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:27 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 445 expanded)
%              Number of leaves         :   43 ( 189 expanded)
%              Depth                    :   15
%              Number of atoms          :  883 (3275 expanded)
%              Number of equality atoms :  243 (1202 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f145,f151,f173,f192,f197,f216,f243,f267,f280,f290,f297,f316,f329,f342,f378,f406,f450,f490,f512,f533])).

fof(f533,plain,
    ( ~ spl5_2
    | spl5_8
    | ~ spl5_13
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_57 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | ~ spl5_2
    | spl5_8
    | ~ spl5_13
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f531,f266])).

fof(f266,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl5_24
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f531,plain,
    ( sK1 != k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_2
    | spl5_8
    | ~ spl5_13
    | ~ spl5_22
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f530,f242])).

fof(f242,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl5_22
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f530,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3)
    | ~ spl5_2
    | spl5_8
    | ~ spl5_13
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f529,f341])).

fof(f341,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl5_35
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f529,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_2
    | spl5_8
    | ~ spl5_13
    | ~ spl5_27
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f528,f286])).

fof(f286,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl5_27
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f528,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_2
    | spl5_8
    | ~ spl5_13
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f527,f150])).

fof(f150,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f527,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_2
    | spl5_8
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f526,f89])).

fof(f89,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f526,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_8
    | ~ spl5_57 ),
    inference(subsumption_resolution,[],[f525,f119])).

fof(f119,plain,
    ( k2_funct_1(sK2) != sK3
    | spl5_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_8
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f525,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_57 ),
    inference(trivial_inequality_removal,[],[f524])).

fof(f524,plain,
    ( k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) != k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_57 ),
    inference(superposition,[],[f57,f511])).

fof(f511,plain,
    ( k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) = k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2),sK3))
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl5_57
  <=> k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) = k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f512,plain,
    ( spl5_57
    | ~ spl5_43
    | ~ spl5_50
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f502,f488,f447,f403,f509])).

fof(f403,plain,
    ( spl5_43
  <=> r2_hidden(sK4(k2_funct_1(sK2),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f447,plain,
    ( spl5_50
  <=> sK4(k2_funct_1(sK2),sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f488,plain,
    ( spl5_55
  <=> ! [X0] :
        ( k1_funct_1(sK3,X0) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,k1_funct_1(sK3,X0)))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f502,plain,
    ( k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) = k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2),sK3))
    | ~ spl5_43
    | ~ spl5_50
    | ~ spl5_55 ),
    inference(forward_demodulation,[],[f500,f449])).

fof(f449,plain,
    ( sK4(k2_funct_1(sK2),sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f447])).

fof(f500,plain,
    ( k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3))))
    | ~ spl5_43
    | ~ spl5_55 ),
    inference(resolution,[],[f489,f405])).

fof(f405,plain,
    ( r2_hidden(sK4(k2_funct_1(sK2),sK3),sK1)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f403])).

fof(f489,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_funct_1(sK3,X0) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,k1_funct_1(sK3,X0))) )
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f488])).

fof(f490,plain,
    ( spl5_55
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f291,f278,f488])).

fof(f278,plain,
    ( spl5_26
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f291,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,X0) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,k1_funct_1(sK3,X0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_26 ),
    inference(resolution,[],[f279,f75])).

fof(f75,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK3,X4),sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK0)
      | k1_funct_1(sK3,X4) != X5
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X4,X5] :
        ( ( ( k1_funct_1(sK3,X4) = X5
            & r2_hidden(X4,sK1) )
          | k1_funct_1(sK2,X5) != X4
          | ~ r2_hidden(X5,sK0) )
        & ( ( k1_funct_1(sK2,X5) = X4
            & r2_hidden(X5,sK0) )
          | k1_funct_1(sK3,X4) != X5
          | ~ r2_hidden(X4,sK1) ) )
    & v2_funct_1(sK2)
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & ! [X4,X5] :
                ( ( ( k1_funct_1(X3,X4) = X5
                    & r2_hidden(X4,X1) )
                  | k1_funct_1(X2,X5) != X4
                  | ~ r2_hidden(X5,X0) )
                & ( ( k1_funct_1(X2,X5) = X4
                    & r2_hidden(X5,X0) )
                  | k1_funct_1(X3,X4) != X5
                  | ~ r2_hidden(X4,X1) ) )
            & v2_funct_1(X2)
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
          & ! [X5,X4] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,sK1) )
                | k1_funct_1(sK2,X5) != X4
                | ~ r2_hidden(X5,sK0) )
              & ( ( k1_funct_1(sK2,X5) = X4
                  & r2_hidden(X5,sK0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,sK1) ) )
          & v2_funct_1(sK2)
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & ! [X5,X4] :
            ( ( ( k1_funct_1(X3,X4) = X5
                & r2_hidden(X4,sK1) )
              | k1_funct_1(sK2,X5) != X4
              | ~ r2_hidden(X5,sK0) )
            & ( ( k1_funct_1(sK2,X5) = X4
                & r2_hidden(X5,sK0) )
              | k1_funct_1(X3,X4) != X5
              | ~ r2_hidden(X4,sK1) ) )
        & v2_funct_1(sK2)
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5,X4] :
          ( ( ( k1_funct_1(sK3,X4) = X5
              & r2_hidden(X4,sK1) )
            | k1_funct_1(sK2,X5) != X4
            | ~ r2_hidden(X5,sK0) )
          & ( ( k1_funct_1(sK2,X5) = X4
              & r2_hidden(X5,sK0) )
            | k1_funct_1(sK3,X4) != X5
            | ~ r2_hidden(X4,sK1) ) )
      & v2_funct_1(sK2)
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) )
                     => ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) ) )
                    & ( ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) )
                     => ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) ) ) )
                & v2_funct_1(X2)
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) )
                   => ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) ) )
                  & ( ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) )
                   => ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) ) ) )
              & v2_funct_1(X2)
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).

fof(f279,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3 )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f278])).

fof(f450,plain,
    ( spl5_50
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f410,f403,f447])).

fof(f410,plain,
    ( sK4(k2_funct_1(sK2),sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)))
    | ~ spl5_43 ),
    inference(resolution,[],[f405,f74])).

fof(f74,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK2,k1_funct_1(sK3,X4)) = X4 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK2,X5) = X4
      | k1_funct_1(sK3,X4) != X5
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f406,plain,
    ( spl5_43
    | spl5_8
    | ~ spl5_24
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f401,f376,f339,f284,f264,f117,f403])).

fof(f376,plain,
    ( spl5_41
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK1
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f401,plain,
    ( r2_hidden(sK4(k2_funct_1(sK2),sK3),sK1)
    | spl5_8
    | ~ spl5_24
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f400,f266])).

fof(f400,plain,
    ( r2_hidden(sK4(k2_funct_1(sK2),sK3),k1_relat_1(k2_funct_1(sK2)))
    | spl5_8
    | ~ spl5_24
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f399,f341])).

fof(f399,plain,
    ( r2_hidden(sK4(k2_funct_1(sK2),sK3),k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_8
    | ~ spl5_24
    | ~ spl5_27
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f398,f266])).

fof(f398,plain,
    ( r2_hidden(sK4(k2_funct_1(sK2),sK3),k1_relat_1(k2_funct_1(sK2)))
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_8
    | ~ spl5_27
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f393,f119])).

fof(f393,plain,
    ( r2_hidden(sK4(k2_funct_1(sK2),sK3),k1_relat_1(k2_funct_1(sK2)))
    | k2_funct_1(sK2) = sK3
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_27
    | ~ spl5_41 ),
    inference(resolution,[],[f377,f286])).

fof(f377,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | k1_relat_1(X0) != sK1
        | ~ v1_relat_1(X0) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f376])).

fof(f378,plain,
    ( spl5_41
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f249,f240,f148,f87,f376])).

fof(f249,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_2
    | ~ spl5_13
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f248,f150])).

fof(f248,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f244,f89])).

fof(f244,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_22 ),
    inference(superposition,[],[f56,f242])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f342,plain,
    ( spl5_35
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f333,f326,f339])).

fof(f326,plain,
    ( spl5_34
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f333,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_34 ),
    inference(resolution,[],[f328,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f51,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f328,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f326])).

fof(f329,plain,
    ( spl5_34
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f324,f314,f132,f122,f107,f326])).

fof(f107,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f122,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f132,plain,
    ( spl5_11
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f314,plain,
    ( spl5_32
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f324,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f323,f109])).

fof(f109,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f323,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f322,f134])).

fof(f134,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f322,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_9
    | ~ spl5_32 ),
    inference(resolution,[],[f315,f124])).

fof(f124,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f314])).

fof(f316,plain,
    ( spl5_32
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f218,f92,f82,f314])).

fof(f82,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f92,plain,
    ( spl5_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

% (21009)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f218,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f217,f84])).

fof(f84,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_3 ),
    inference(resolution,[],[f71,f94])).

fof(f94,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f297,plain,
    ( ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f295,f134])).

fof(f295,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f293,f109])).

fof(f293,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_9
    | ~ spl5_28 ),
    inference(resolution,[],[f289,f124])).

fof(f289,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl5_28
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f290,plain,
    ( spl5_27
    | spl5_28
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f203,f92,f82,f288,f284])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f202,f84])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_3 ),
    inference(resolution,[],[f69,f94])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f280,plain,
    ( spl5_26
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f232,f213,f142,f92,f82,f278])).

fof(f142,plain,
    ( spl5_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f213,plain,
    ( spl5_20
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f232,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3 )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f231,f144])).

fof(f144,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f231,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3
        | ~ v1_relat_1(sK2) )
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f230,f84])).

fof(f230,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f222,f94])).

fof(f222,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl5_20 ),
    inference(superposition,[],[f59,f215])).

fof(f215,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f267,plain,
    ( spl5_24
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f262,f170,f142,f92,f82,f264])).

fof(f170,plain,
    ( spl5_15
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f262,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(forward_demodulation,[],[f261,f172])).

fof(f172,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f261,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f153,f144])).

fof(f153,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f152,f84])).

fof(f152,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f54,f94])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f243,plain,
    ( spl5_22
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f238,f194,f127,f240])).

fof(f127,plain,
    ( spl5_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f194,plain,
    ( spl5_19
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f238,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f160,f196])).

fof(f196,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f194])).

% (21020)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (21007)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (21016)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f160,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,sK0,sK3)
    | ~ spl5_10 ),
    inference(resolution,[],[f61,f129])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f216,plain,
    ( spl5_20
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f208,f189,f122,f213])).

fof(f189,plain,
    ( spl5_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f208,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_9
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f159,f191])).

fof(f191,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f159,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f61,f124])).

fof(f197,plain,
    ( spl5_19
    | spl5_4
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f187,f127,f112,f97,f194])).

fof(f97,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f112,plain,
    ( spl5_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f187,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl5_4
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f186,f99])).

fof(f99,plain,
    ( k1_xboole_0 != sK0
    | spl5_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f186,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f183,f114])).

fof(f114,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f183,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl5_10 ),
    inference(resolution,[],[f63,f129])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f192,plain,
    ( spl5_18
    | spl5_5
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f185,f122,f107,f102,f189])).

fof(f102,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f185,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl5_5
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f184,f104])).

fof(f104,plain,
    ( k1_xboole_0 != sK1
    | spl5_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f184,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f182,f109])).

fof(f182,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f63,f124])).

fof(f173,plain,
    ( spl5_15
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f168,f132,f122,f170])).

fof(f168,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f166,f134])).

fof(f166,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f62,f124])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f151,plain,
    ( spl5_13
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f139,f127,f148])).

fof(f139,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_10 ),
    inference(resolution,[],[f136,f129])).

fof(f145,plain,
    ( spl5_12
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f138,f122,f142])).

fof(f138,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f136,f124])).

fof(f135,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f42,f132])).

fof(f42,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f130,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f41,f127])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f125,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f38,f122])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f120,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f50,f117])).

fof(f50,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f115,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f40,f112])).

fof(f40,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f110,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f37,f107])).

fof(f37,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f49,f102])).

fof(f49,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f48,f97])).

fof(f48,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f43,f92])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f87])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

% (21001)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f85,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (21002)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (21010)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (20998)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.26/0.52  % (21006)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.26/0.52  % (21014)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.26/0.52  % (20997)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.52  % (21021)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.26/0.52  % (20996)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.26/0.53  % (21012)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.26/0.53  % (21000)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.26/0.53  % (21005)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.26/0.53  % (21003)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.42/0.54  % (20999)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.42/0.54  % (21004)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.42/0.54  % (21017)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.42/0.54  % (21013)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.42/0.54  % (20998)Refutation found. Thanks to Tanya!
% 1.42/0.54  % SZS status Theorem for theBenchmark
% 1.42/0.54  % SZS output start Proof for theBenchmark
% 1.42/0.54  fof(f534,plain,(
% 1.42/0.54    $false),
% 1.42/0.54    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f145,f151,f173,f192,f197,f216,f243,f267,f280,f290,f297,f316,f329,f342,f378,f406,f450,f490,f512,f533])).
% 1.42/0.54  fof(f533,plain,(
% 1.42/0.54    ~spl5_2 | spl5_8 | ~spl5_13 | ~spl5_22 | ~spl5_24 | ~spl5_27 | ~spl5_35 | ~spl5_57),
% 1.42/0.54    inference(avatar_contradiction_clause,[],[f532])).
% 1.42/0.54  fof(f532,plain,(
% 1.42/0.54    $false | (~spl5_2 | spl5_8 | ~spl5_13 | ~spl5_22 | ~spl5_24 | ~spl5_27 | ~spl5_35 | ~spl5_57)),
% 1.42/0.54    inference(subsumption_resolution,[],[f531,f266])).
% 1.42/0.54  fof(f266,plain,(
% 1.42/0.54    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl5_24),
% 1.42/0.54    inference(avatar_component_clause,[],[f264])).
% 1.42/0.54  fof(f264,plain,(
% 1.42/0.54    spl5_24 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.42/0.54  fof(f531,plain,(
% 1.42/0.54    sK1 != k1_relat_1(k2_funct_1(sK2)) | (~spl5_2 | spl5_8 | ~spl5_13 | ~spl5_22 | ~spl5_27 | ~spl5_35 | ~spl5_57)),
% 1.42/0.54    inference(forward_demodulation,[],[f530,f242])).
% 1.42/0.54  fof(f242,plain,(
% 1.42/0.54    sK1 = k1_relat_1(sK3) | ~spl5_22),
% 1.42/0.54    inference(avatar_component_clause,[],[f240])).
% 1.42/0.54  fof(f240,plain,(
% 1.42/0.54    spl5_22 <=> sK1 = k1_relat_1(sK3)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.42/0.54  fof(f530,plain,(
% 1.42/0.54    k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3) | (~spl5_2 | spl5_8 | ~spl5_13 | ~spl5_27 | ~spl5_35 | ~spl5_57)),
% 1.42/0.54    inference(subsumption_resolution,[],[f529,f341])).
% 1.42/0.54  fof(f341,plain,(
% 1.42/0.54    v1_relat_1(k2_funct_1(sK2)) | ~spl5_35),
% 1.42/0.54    inference(avatar_component_clause,[],[f339])).
% 1.42/0.54  fof(f339,plain,(
% 1.42/0.54    spl5_35 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.42/0.54  fof(f529,plain,(
% 1.42/0.54    k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_2 | spl5_8 | ~spl5_13 | ~spl5_27 | ~spl5_57)),
% 1.42/0.54    inference(subsumption_resolution,[],[f528,f286])).
% 1.42/0.54  fof(f286,plain,(
% 1.42/0.54    v1_funct_1(k2_funct_1(sK2)) | ~spl5_27),
% 1.42/0.54    inference(avatar_component_clause,[],[f284])).
% 1.42/0.54  fof(f284,plain,(
% 1.42/0.54    spl5_27 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.42/0.54  fof(f528,plain,(
% 1.42/0.54    k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_2 | spl5_8 | ~spl5_13 | ~spl5_57)),
% 1.42/0.54    inference(subsumption_resolution,[],[f527,f150])).
% 1.42/0.54  fof(f150,plain,(
% 1.42/0.54    v1_relat_1(sK3) | ~spl5_13),
% 1.42/0.54    inference(avatar_component_clause,[],[f148])).
% 1.42/0.54  fof(f148,plain,(
% 1.42/0.54    spl5_13 <=> v1_relat_1(sK3)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.42/0.54  fof(f527,plain,(
% 1.42/0.54    k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_2 | spl5_8 | ~spl5_57)),
% 1.42/0.54    inference(subsumption_resolution,[],[f526,f89])).
% 1.42/0.54  fof(f89,plain,(
% 1.42/0.54    v1_funct_1(sK3) | ~spl5_2),
% 1.42/0.54    inference(avatar_component_clause,[],[f87])).
% 1.42/0.54  fof(f87,plain,(
% 1.42/0.54    spl5_2 <=> v1_funct_1(sK3)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.42/0.54  fof(f526,plain,(
% 1.42/0.54    k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (spl5_8 | ~spl5_57)),
% 1.42/0.54    inference(subsumption_resolution,[],[f525,f119])).
% 1.42/0.54  fof(f119,plain,(
% 1.42/0.54    k2_funct_1(sK2) != sK3 | spl5_8),
% 1.42/0.54    inference(avatar_component_clause,[],[f117])).
% 1.42/0.54  fof(f117,plain,(
% 1.42/0.54    spl5_8 <=> k2_funct_1(sK2) = sK3),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.42/0.54  fof(f525,plain,(
% 1.42/0.54    k2_funct_1(sK2) = sK3 | k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_57),
% 1.42/0.54    inference(trivial_inequality_removal,[],[f524])).
% 1.42/0.54  fof(f524,plain,(
% 1.42/0.54    k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) != k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) | k2_funct_1(sK2) = sK3 | k1_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_57),
% 1.42/0.54    inference(superposition,[],[f57,f511])).
% 1.42/0.54  fof(f511,plain,(
% 1.42/0.54    k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) = k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2),sK3)) | ~spl5_57),
% 1.42/0.54    inference(avatar_component_clause,[],[f509])).
% 1.42/0.54  fof(f509,plain,(
% 1.42/0.54    spl5_57 <=> k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) = k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2),sK3))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 1.42/0.54  fof(f57,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f34])).
% 1.42/0.54  fof(f34,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f33])).
% 1.42/0.54  fof(f33,plain,(
% 1.42/0.54    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f21,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(flattening,[],[f20])).
% 1.42/0.54  fof(f20,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.42/0.54  fof(f512,plain,(
% 1.42/0.54    spl5_57 | ~spl5_43 | ~spl5_50 | ~spl5_55),
% 1.42/0.54    inference(avatar_split_clause,[],[f502,f488,f447,f403,f509])).
% 1.42/0.54  fof(f403,plain,(
% 1.42/0.54    spl5_43 <=> r2_hidden(sK4(k2_funct_1(sK2),sK3),sK1)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 1.42/0.54  fof(f447,plain,(
% 1.42/0.54    spl5_50 <=> sK4(k2_funct_1(sK2),sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 1.42/0.54  fof(f488,plain,(
% 1.42/0.54    spl5_55 <=> ! [X0] : (k1_funct_1(sK3,X0) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,k1_funct_1(sK3,X0))) | ~r2_hidden(X0,sK1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 1.42/0.54  fof(f502,plain,(
% 1.42/0.54    k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) = k1_funct_1(k2_funct_1(sK2),sK4(k2_funct_1(sK2),sK3)) | (~spl5_43 | ~spl5_50 | ~spl5_55)),
% 1.42/0.54    inference(forward_demodulation,[],[f500,f449])).
% 1.42/0.54  fof(f449,plain,(
% 1.42/0.54    sK4(k2_funct_1(sK2),sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3))) | ~spl5_50),
% 1.42/0.54    inference(avatar_component_clause,[],[f447])).
% 1.42/0.54  fof(f500,plain,(
% 1.42/0.54    k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3)))) | (~spl5_43 | ~spl5_55)),
% 1.42/0.54    inference(resolution,[],[f489,f405])).
% 1.42/0.54  fof(f405,plain,(
% 1.42/0.54    r2_hidden(sK4(k2_funct_1(sK2),sK3),sK1) | ~spl5_43),
% 1.42/0.54    inference(avatar_component_clause,[],[f403])).
% 1.42/0.54  fof(f489,plain,(
% 1.42/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(sK3,X0) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,k1_funct_1(sK3,X0)))) ) | ~spl5_55),
% 1.42/0.54    inference(avatar_component_clause,[],[f488])).
% 1.42/0.54  fof(f490,plain,(
% 1.42/0.54    spl5_55 | ~spl5_26),
% 1.42/0.54    inference(avatar_split_clause,[],[f291,f278,f488])).
% 1.42/0.54  fof(f278,plain,(
% 1.42/0.54    spl5_26 <=> ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.42/0.54  fof(f291,plain,(
% 1.42/0.54    ( ! [X0] : (k1_funct_1(sK3,X0) = k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,k1_funct_1(sK3,X0))) | ~r2_hidden(X0,sK1)) ) | ~spl5_26),
% 1.42/0.54    inference(resolution,[],[f279,f75])).
% 1.42/0.54  fof(f75,plain,(
% 1.42/0.54    ( ! [X4] : (r2_hidden(k1_funct_1(sK3,X4),sK0) | ~r2_hidden(X4,sK1)) )),
% 1.42/0.54    inference(equality_resolution,[],[f44])).
% 1.42/0.54  fof(f44,plain,(
% 1.42/0.54    ( ! [X4,X5] : (r2_hidden(X5,sK0) | k1_funct_1(sK3,X4) != X5 | ~r2_hidden(X4,sK1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f32])).
% 1.42/0.54  fof(f32,plain,(
% 1.42/0.54    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X4,X5] : (((k1_funct_1(sK3,X4) = X5 & r2_hidden(X4,sK1)) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) & ((k1_funct_1(sK2,X5) = X4 & r2_hidden(X5,sK0)) | k1_funct_1(sK3,X4) != X5 | ~r2_hidden(X4,sK1))) & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f31,f30])).
% 1.42/0.54  fof(f30,plain,(
% 1.42/0.54    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK1)) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) & ((k1_funct_1(sK2,X5) = X4 & r2_hidden(X5,sK0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK1))) & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f31,plain,(
% 1.42/0.54    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK1)) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) & ((k1_funct_1(sK2,X5) = X4 & r2_hidden(X5,sK0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK1))) & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5,X4] : (((k1_funct_1(sK3,X4) = X5 & r2_hidden(X4,sK1)) | k1_funct_1(sK2,X5) != X4 | ~r2_hidden(X5,sK0)) & ((k1_funct_1(sK2,X5) = X4 & r2_hidden(X5,sK0)) | k1_funct_1(sK3,X4) != X5 | ~r2_hidden(X4,sK1))) & v2_funct_1(sK2) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f14,plain,(
% 1.42/0.54    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.42/0.54    inference(flattening,[],[f13])).
% 1.42/0.54  fof(f13,plain,(
% 1.42/0.54    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | (k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0))) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | (k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.42/0.54    inference(ennf_transformation,[],[f12])).
% 1.42/0.54  fof(f12,negated_conjecture,(
% 1.42/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.42/0.54    inference(negated_conjecture,[],[f11])).
% 1.42/0.54  fof(f11,conjecture,(
% 1.42/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).
% 1.42/0.54  fof(f279,plain,(
% 1.42/0.54    ( ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3) ) | ~spl5_26),
% 1.42/0.54    inference(avatar_component_clause,[],[f278])).
% 1.42/0.54  fof(f450,plain,(
% 1.42/0.54    spl5_50 | ~spl5_43),
% 1.42/0.54    inference(avatar_split_clause,[],[f410,f403,f447])).
% 1.42/0.54  fof(f410,plain,(
% 1.42/0.54    sK4(k2_funct_1(sK2),sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(k2_funct_1(sK2),sK3))) | ~spl5_43),
% 1.42/0.54    inference(resolution,[],[f405,f74])).
% 1.42/0.54  fof(f74,plain,(
% 1.42/0.54    ( ! [X4] : (~r2_hidden(X4,sK1) | k1_funct_1(sK2,k1_funct_1(sK3,X4)) = X4) )),
% 1.42/0.54    inference(equality_resolution,[],[f45])).
% 1.42/0.54  fof(f45,plain,(
% 1.42/0.54    ( ! [X4,X5] : (k1_funct_1(sK2,X5) = X4 | k1_funct_1(sK3,X4) != X5 | ~r2_hidden(X4,sK1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f32])).
% 1.42/0.54  fof(f406,plain,(
% 1.42/0.54    spl5_43 | spl5_8 | ~spl5_24 | ~spl5_27 | ~spl5_35 | ~spl5_41),
% 1.42/0.54    inference(avatar_split_clause,[],[f401,f376,f339,f284,f264,f117,f403])).
% 1.42/0.54  fof(f376,plain,(
% 1.42/0.54    spl5_41 <=> ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.42/0.54  fof(f401,plain,(
% 1.42/0.54    r2_hidden(sK4(k2_funct_1(sK2),sK3),sK1) | (spl5_8 | ~spl5_24 | ~spl5_27 | ~spl5_35 | ~spl5_41)),
% 1.42/0.54    inference(forward_demodulation,[],[f400,f266])).
% 1.42/0.54  fof(f400,plain,(
% 1.42/0.54    r2_hidden(sK4(k2_funct_1(sK2),sK3),k1_relat_1(k2_funct_1(sK2))) | (spl5_8 | ~spl5_24 | ~spl5_27 | ~spl5_35 | ~spl5_41)),
% 1.42/0.54    inference(subsumption_resolution,[],[f399,f341])).
% 1.42/0.54  fof(f399,plain,(
% 1.42/0.54    r2_hidden(sK4(k2_funct_1(sK2),sK3),k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (spl5_8 | ~spl5_24 | ~spl5_27 | ~spl5_41)),
% 1.42/0.54    inference(subsumption_resolution,[],[f398,f266])).
% 1.42/0.54  fof(f398,plain,(
% 1.42/0.54    r2_hidden(sK4(k2_funct_1(sK2),sK3),k1_relat_1(k2_funct_1(sK2))) | sK1 != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (spl5_8 | ~spl5_27 | ~spl5_41)),
% 1.42/0.54    inference(subsumption_resolution,[],[f393,f119])).
% 1.42/0.54  fof(f393,plain,(
% 1.42/0.54    r2_hidden(sK4(k2_funct_1(sK2),sK3),k1_relat_1(k2_funct_1(sK2))) | k2_funct_1(sK2) = sK3 | sK1 != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_27 | ~spl5_41)),
% 1.42/0.54    inference(resolution,[],[f377,f286])).
% 1.42/0.54  fof(f377,plain,(
% 1.42/0.54    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0 | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0)) ) | ~spl5_41),
% 1.42/0.54    inference(avatar_component_clause,[],[f376])).
% 1.42/0.54  fof(f378,plain,(
% 1.42/0.54    spl5_41 | ~spl5_2 | ~spl5_13 | ~spl5_22),
% 1.42/0.54    inference(avatar_split_clause,[],[f249,f240,f148,f87,f376])).
% 1.42/0.54  fof(f249,plain,(
% 1.42/0.54    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl5_2 | ~spl5_13 | ~spl5_22)),
% 1.42/0.54    inference(subsumption_resolution,[],[f248,f150])).
% 1.42/0.54  fof(f248,plain,(
% 1.42/0.54    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0 | ~v1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl5_2 | ~spl5_22)),
% 1.42/0.54    inference(subsumption_resolution,[],[f244,f89])).
% 1.42/0.54  fof(f244,plain,(
% 1.42/0.54    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_22),
% 1.42/0.54    inference(superposition,[],[f56,f242])).
% 1.42/0.54  fof(f56,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f34])).
% 1.42/0.54  fof(f342,plain,(
% 1.42/0.54    spl5_35 | ~spl5_34),
% 1.42/0.54    inference(avatar_split_clause,[],[f333,f326,f339])).
% 1.42/0.54  fof(f326,plain,(
% 1.42/0.54    spl5_34 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.42/0.54  fof(f333,plain,(
% 1.42/0.54    v1_relat_1(k2_funct_1(sK2)) | ~spl5_34),
% 1.42/0.54    inference(resolution,[],[f328,f136])).
% 1.42/0.54  fof(f136,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.42/0.54    inference(resolution,[],[f51,f58])).
% 1.42/0.54  fof(f58,plain,(
% 1.42/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f2])).
% 1.42/0.54  fof(f2,axiom,(
% 1.42/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.42/0.54  fof(f51,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f15])).
% 1.42/0.54  fof(f15,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f1])).
% 1.42/0.54  fof(f1,axiom,(
% 1.42/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.42/0.54  fof(f328,plain,(
% 1.42/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_34),
% 1.42/0.54    inference(avatar_component_clause,[],[f326])).
% 1.42/0.54  fof(f329,plain,(
% 1.42/0.54    spl5_34 | ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_32),
% 1.42/0.54    inference(avatar_split_clause,[],[f324,f314,f132,f122,f107,f326])).
% 1.42/0.54  fof(f107,plain,(
% 1.42/0.54    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.42/0.54  fof(f122,plain,(
% 1.42/0.54    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.42/0.54  fof(f132,plain,(
% 1.42/0.54    spl5_11 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.42/0.54  fof(f314,plain,(
% 1.42/0.54    spl5_32 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.42/0.54  fof(f324,plain,(
% 1.42/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_32)),
% 1.42/0.54    inference(subsumption_resolution,[],[f323,f109])).
% 1.42/0.54  fof(f109,plain,(
% 1.42/0.54    v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 1.42/0.54    inference(avatar_component_clause,[],[f107])).
% 1.42/0.54  fof(f323,plain,(
% 1.42/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK2,sK0,sK1) | (~spl5_9 | ~spl5_11 | ~spl5_32)),
% 1.42/0.54    inference(subsumption_resolution,[],[f322,f134])).
% 1.42/0.54  fof(f134,plain,(
% 1.42/0.54    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_11),
% 1.42/0.54    inference(avatar_component_clause,[],[f132])).
% 1.42/0.54  fof(f322,plain,(
% 1.42/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | (~spl5_9 | ~spl5_32)),
% 1.42/0.54    inference(resolution,[],[f315,f124])).
% 1.42/0.54  fof(f124,plain,(
% 1.42/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_9),
% 1.42/0.54    inference(avatar_component_clause,[],[f122])).
% 1.42/0.54  fof(f315,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1)) ) | ~spl5_32),
% 1.42/0.54    inference(avatar_component_clause,[],[f314])).
% 1.42/0.54  fof(f316,plain,(
% 1.42/0.54    spl5_32 | ~spl5_1 | ~spl5_3),
% 1.42/0.54    inference(avatar_split_clause,[],[f218,f92,f82,f314])).
% 1.42/0.54  fof(f82,plain,(
% 1.42/0.54    spl5_1 <=> v1_funct_1(sK2)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.42/0.54  fof(f92,plain,(
% 1.42/0.54    spl5_3 <=> v2_funct_1(sK2)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.42/0.54  % (21009)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.42/0.54  fof(f218,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1)) ) | (~spl5_1 | ~spl5_3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f217,f84])).
% 1.42/0.54  fof(f84,plain,(
% 1.42/0.54    v1_funct_1(sK2) | ~spl5_1),
% 1.42/0.54    inference(avatar_component_clause,[],[f82])).
% 1.42/0.54  fof(f217,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl5_3),
% 1.42/0.54    inference(resolution,[],[f71,f94])).
% 1.42/0.54  fof(f94,plain,(
% 1.42/0.54    v2_funct_1(sK2) | ~spl5_3),
% 1.42/0.54    inference(avatar_component_clause,[],[f92])).
% 1.42/0.54  fof(f71,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f29,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.42/0.54    inference(flattening,[],[f28])).
% 1.42/0.54  fof(f28,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.42/0.54    inference(ennf_transformation,[],[f10])).
% 1.42/0.54  fof(f10,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.42/0.54  fof(f297,plain,(
% 1.42/0.54    ~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_28),
% 1.42/0.54    inference(avatar_contradiction_clause,[],[f296])).
% 1.42/0.54  fof(f296,plain,(
% 1.42/0.54    $false | (~spl5_6 | ~spl5_9 | ~spl5_11 | ~spl5_28)),
% 1.42/0.54    inference(subsumption_resolution,[],[f295,f134])).
% 1.42/0.54  fof(f295,plain,(
% 1.42/0.54    sK1 != k2_relset_1(sK0,sK1,sK2) | (~spl5_6 | ~spl5_9 | ~spl5_28)),
% 1.42/0.54    inference(subsumption_resolution,[],[f293,f109])).
% 1.42/0.54  fof(f293,plain,(
% 1.42/0.54    ~v1_funct_2(sK2,sK0,sK1) | sK1 != k2_relset_1(sK0,sK1,sK2) | (~spl5_9 | ~spl5_28)),
% 1.42/0.54    inference(resolution,[],[f289,f124])).
% 1.42/0.54  fof(f289,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl5_28),
% 1.42/0.54    inference(avatar_component_clause,[],[f288])).
% 1.42/0.54  fof(f288,plain,(
% 1.42/0.54    spl5_28 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.42/0.54  fof(f290,plain,(
% 1.42/0.54    spl5_27 | spl5_28 | ~spl5_1 | ~spl5_3),
% 1.42/0.54    inference(avatar_split_clause,[],[f203,f92,f82,f288,f284])).
% 1.42/0.54  fof(f203,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1)) ) | (~spl5_1 | ~spl5_3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f202,f84])).
% 1.42/0.54  fof(f202,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl5_3),
% 1.42/0.54    inference(resolution,[],[f69,f94])).
% 1.42/0.54  fof(f69,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f280,plain,(
% 1.42/0.54    spl5_26 | ~spl5_1 | ~spl5_3 | ~spl5_12 | ~spl5_20),
% 1.42/0.54    inference(avatar_split_clause,[],[f232,f213,f142,f92,f82,f278])).
% 1.42/0.54  fof(f142,plain,(
% 1.42/0.54    spl5_12 <=> v1_relat_1(sK2)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.42/0.54  fof(f213,plain,(
% 1.42/0.54    spl5_20 <=> sK0 = k1_relat_1(sK2)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.42/0.54  fof(f232,plain,(
% 1.42/0.54    ( ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3) ) | (~spl5_1 | ~spl5_3 | ~spl5_12 | ~spl5_20)),
% 1.42/0.54    inference(subsumption_resolution,[],[f231,f144])).
% 1.42/0.54  fof(f144,plain,(
% 1.42/0.54    v1_relat_1(sK2) | ~spl5_12),
% 1.42/0.54    inference(avatar_component_clause,[],[f142])).
% 1.42/0.54  fof(f231,plain,(
% 1.42/0.54    ( ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3 | ~v1_relat_1(sK2)) ) | (~spl5_1 | ~spl5_3 | ~spl5_20)),
% 1.42/0.54    inference(subsumption_resolution,[],[f230,f84])).
% 1.42/0.54  fof(f230,plain,(
% 1.42/0.54    ( ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl5_3 | ~spl5_20)),
% 1.42/0.54    inference(subsumption_resolution,[],[f222,f94])).
% 1.42/0.54  fof(f222,plain,(
% 1.42/0.54    ( ! [X3] : (~r2_hidden(X3,sK0) | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X3)) = X3 | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl5_20),
% 1.42/0.54    inference(superposition,[],[f59,f215])).
% 1.42/0.54  fof(f215,plain,(
% 1.42/0.54    sK0 = k1_relat_1(sK2) | ~spl5_20),
% 1.42/0.54    inference(avatar_component_clause,[],[f213])).
% 1.42/0.54  fof(f59,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f23])).
% 1.42/0.54  fof(f23,plain,(
% 1.42/0.54    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.42/0.54    inference(flattening,[],[f22])).
% 1.42/0.54  fof(f22,plain,(
% 1.42/0.54    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.42/0.54    inference(ennf_transformation,[],[f5])).
% 1.42/0.54  fof(f5,axiom,(
% 1.42/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 1.42/0.54  fof(f267,plain,(
% 1.42/0.54    spl5_24 | ~spl5_1 | ~spl5_3 | ~spl5_12 | ~spl5_15),
% 1.42/0.54    inference(avatar_split_clause,[],[f262,f170,f142,f92,f82,f264])).
% 1.42/0.54  fof(f170,plain,(
% 1.42/0.54    spl5_15 <=> sK1 = k2_relat_1(sK2)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.42/0.54  fof(f262,plain,(
% 1.42/0.54    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_3 | ~spl5_12 | ~spl5_15)),
% 1.42/0.54    inference(forward_demodulation,[],[f261,f172])).
% 1.42/0.54  fof(f172,plain,(
% 1.42/0.54    sK1 = k2_relat_1(sK2) | ~spl5_15),
% 1.42/0.54    inference(avatar_component_clause,[],[f170])).
% 1.42/0.54  fof(f261,plain,(
% 1.42/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_3 | ~spl5_12)),
% 1.42/0.54    inference(subsumption_resolution,[],[f153,f144])).
% 1.42/0.54  fof(f153,plain,(
% 1.42/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl5_1 | ~spl5_3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f152,f84])).
% 1.42/0.54  fof(f152,plain,(
% 1.42/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_3),
% 1.42/0.54    inference(resolution,[],[f54,f94])).
% 1.42/0.54  fof(f54,plain,(
% 1.42/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f19])).
% 1.42/0.54  fof(f19,plain,(
% 1.42/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(flattening,[],[f18])).
% 1.42/0.54  fof(f18,plain,(
% 1.42/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f4])).
% 1.42/0.54  fof(f4,axiom,(
% 1.42/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.42/0.54  fof(f243,plain,(
% 1.42/0.54    spl5_22 | ~spl5_10 | ~spl5_19),
% 1.42/0.54    inference(avatar_split_clause,[],[f238,f194,f127,f240])).
% 1.42/0.54  fof(f127,plain,(
% 1.42/0.54    spl5_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.42/0.54  fof(f194,plain,(
% 1.42/0.54    spl5_19 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.42/0.54  fof(f238,plain,(
% 1.42/0.54    sK1 = k1_relat_1(sK3) | (~spl5_10 | ~spl5_19)),
% 1.42/0.54    inference(forward_demodulation,[],[f160,f196])).
% 1.42/0.54  fof(f196,plain,(
% 1.42/0.54    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl5_19),
% 1.42/0.54    inference(avatar_component_clause,[],[f194])).
% 1.42/0.55  % (21020)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.42/0.55  % (21007)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.42/0.55  % (21016)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.42/0.55  fof(f160,plain,(
% 1.42/0.55    k1_relat_1(sK3) = k1_relset_1(sK1,sK0,sK3) | ~spl5_10),
% 1.42/0.55    inference(resolution,[],[f61,f129])).
% 1.42/0.55  fof(f129,plain,(
% 1.42/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_10),
% 1.42/0.55    inference(avatar_component_clause,[],[f127])).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.42/0.55  fof(f216,plain,(
% 1.42/0.55    spl5_20 | ~spl5_9 | ~spl5_18),
% 1.42/0.55    inference(avatar_split_clause,[],[f208,f189,f122,f213])).
% 1.42/0.55  fof(f189,plain,(
% 1.42/0.55    spl5_18 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.42/0.55  fof(f208,plain,(
% 1.42/0.55    sK0 = k1_relat_1(sK2) | (~spl5_9 | ~spl5_18)),
% 1.42/0.55    inference(forward_demodulation,[],[f159,f191])).
% 1.42/0.55  fof(f191,plain,(
% 1.42/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_18),
% 1.42/0.55    inference(avatar_component_clause,[],[f189])).
% 1.42/0.55  fof(f159,plain,(
% 1.42/0.55    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_9),
% 1.42/0.55    inference(resolution,[],[f61,f124])).
% 1.42/0.55  fof(f197,plain,(
% 1.42/0.55    spl5_19 | spl5_4 | ~spl5_7 | ~spl5_10),
% 1.42/0.55    inference(avatar_split_clause,[],[f187,f127,f112,f97,f194])).
% 1.42/0.55  fof(f97,plain,(
% 1.42/0.55    spl5_4 <=> k1_xboole_0 = sK0),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.42/0.55  fof(f112,plain,(
% 1.42/0.55    spl5_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.42/0.55  fof(f187,plain,(
% 1.42/0.55    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl5_4 | ~spl5_7 | ~spl5_10)),
% 1.42/0.55    inference(subsumption_resolution,[],[f186,f99])).
% 1.42/0.55  fof(f99,plain,(
% 1.42/0.55    k1_xboole_0 != sK0 | spl5_4),
% 1.42/0.55    inference(avatar_component_clause,[],[f97])).
% 1.42/0.55  fof(f186,plain,(
% 1.42/0.55    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl5_7 | ~spl5_10)),
% 1.42/0.55    inference(subsumption_resolution,[],[f183,f114])).
% 1.42/0.55  fof(f114,plain,(
% 1.42/0.55    v1_funct_2(sK3,sK1,sK0) | ~spl5_7),
% 1.42/0.55    inference(avatar_component_clause,[],[f112])).
% 1.42/0.55  fof(f183,plain,(
% 1.42/0.55    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl5_10),
% 1.42/0.55    inference(resolution,[],[f63,f129])).
% 1.42/0.55  fof(f63,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f35])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(nnf_transformation,[],[f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(flattening,[],[f26])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.42/0.55  fof(f192,plain,(
% 1.42/0.55    spl5_18 | spl5_5 | ~spl5_6 | ~spl5_9),
% 1.42/0.55    inference(avatar_split_clause,[],[f185,f122,f107,f102,f189])).
% 1.42/0.55  fof(f102,plain,(
% 1.42/0.55    spl5_5 <=> k1_xboole_0 = sK1),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.42/0.55  fof(f185,plain,(
% 1.42/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl5_5 | ~spl5_6 | ~spl5_9)),
% 1.42/0.55    inference(subsumption_resolution,[],[f184,f104])).
% 1.42/0.55  fof(f104,plain,(
% 1.42/0.55    k1_xboole_0 != sK1 | spl5_5),
% 1.42/0.55    inference(avatar_component_clause,[],[f102])).
% 1.42/0.55  fof(f184,plain,(
% 1.42/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl5_6 | ~spl5_9)),
% 1.42/0.55    inference(subsumption_resolution,[],[f182,f109])).
% 1.42/0.55  fof(f182,plain,(
% 1.42/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_9),
% 1.42/0.55    inference(resolution,[],[f63,f124])).
% 1.42/0.55  fof(f173,plain,(
% 1.42/0.55    spl5_15 | ~spl5_9 | ~spl5_11),
% 1.42/0.55    inference(avatar_split_clause,[],[f168,f132,f122,f170])).
% 1.42/0.55  fof(f168,plain,(
% 1.42/0.55    sK1 = k2_relat_1(sK2) | (~spl5_9 | ~spl5_11)),
% 1.42/0.55    inference(forward_demodulation,[],[f166,f134])).
% 1.42/0.55  fof(f166,plain,(
% 1.42/0.55    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl5_9),
% 1.42/0.55    inference(resolution,[],[f62,f124])).
% 1.42/0.55  fof(f62,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.42/0.55  fof(f151,plain,(
% 1.42/0.55    spl5_13 | ~spl5_10),
% 1.42/0.55    inference(avatar_split_clause,[],[f139,f127,f148])).
% 1.42/0.55  fof(f139,plain,(
% 1.42/0.55    v1_relat_1(sK3) | ~spl5_10),
% 1.42/0.55    inference(resolution,[],[f136,f129])).
% 1.42/0.55  fof(f145,plain,(
% 1.42/0.55    spl5_12 | ~spl5_9),
% 1.42/0.55    inference(avatar_split_clause,[],[f138,f122,f142])).
% 1.42/0.55  fof(f138,plain,(
% 1.42/0.55    v1_relat_1(sK2) | ~spl5_9),
% 1.42/0.55    inference(resolution,[],[f136,f124])).
% 1.42/0.55  fof(f135,plain,(
% 1.42/0.55    spl5_11),
% 1.42/0.55    inference(avatar_split_clause,[],[f42,f132])).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f130,plain,(
% 1.42/0.55    spl5_10),
% 1.42/0.55    inference(avatar_split_clause,[],[f41,f127])).
% 1.42/0.55  fof(f41,plain,(
% 1.42/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f125,plain,(
% 1.42/0.55    spl5_9),
% 1.42/0.55    inference(avatar_split_clause,[],[f38,f122])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f120,plain,(
% 1.42/0.55    ~spl5_8),
% 1.42/0.55    inference(avatar_split_clause,[],[f50,f117])).
% 1.42/0.55  fof(f50,plain,(
% 1.42/0.55    k2_funct_1(sK2) != sK3),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f115,plain,(
% 1.42/0.55    spl5_7),
% 1.42/0.55    inference(avatar_split_clause,[],[f40,f112])).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f110,plain,(
% 1.42/0.55    spl5_6),
% 1.42/0.55    inference(avatar_split_clause,[],[f37,f107])).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f105,plain,(
% 1.42/0.55    ~spl5_5),
% 1.42/0.55    inference(avatar_split_clause,[],[f49,f102])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    k1_xboole_0 != sK1),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f100,plain,(
% 1.42/0.55    ~spl5_4),
% 1.42/0.55    inference(avatar_split_clause,[],[f48,f97])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    k1_xboole_0 != sK0),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f95,plain,(
% 1.42/0.55    spl5_3),
% 1.42/0.55    inference(avatar_split_clause,[],[f43,f92])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    v2_funct_1(sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  fof(f90,plain,(
% 1.42/0.55    spl5_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f39,f87])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    v1_funct_1(sK3)),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  % (21001)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.42/0.55  fof(f85,plain,(
% 1.42/0.55    spl5_1),
% 1.42/0.55    inference(avatar_split_clause,[],[f36,f82])).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    v1_funct_1(sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f32])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (20998)------------------------------
% 1.42/0.55  % (20998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (20998)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (20998)Memory used [KB]: 6524
% 1.42/0.55  % (20998)Time elapsed: 0.135 s
% 1.42/0.55  % (20998)------------------------------
% 1.42/0.55  % (20998)------------------------------
% 1.42/0.55  % (20995)Success in time 0.193 s
%------------------------------------------------------------------------------
