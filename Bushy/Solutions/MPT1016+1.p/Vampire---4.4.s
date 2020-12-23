%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t77_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:49 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 489 expanded)
%              Number of leaves         :   11 ( 128 expanded)
%              Depth                    :   21
%              Number of atoms          :  347 (4305 expanded)
%              Number of equality atoms :   99 (1297 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f178,f221])).

fof(f221,plain,
    ( ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f219,f195])).

fof(f195,plain,
    ( sK2 != sK3
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f62,f82])).

fof(f82,plain,
    ( v2_funct_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_0
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f62,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ( sK2 != sK3
        & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,sK0)
        & r2_hidden(sK2,sK0) )
      | ~ v2_funct_1(sK1) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
          | ~ r2_hidden(X5,sK0)
          | ~ r2_hidden(X4,sK0) )
      | v2_funct_1(sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f45,f47,f46])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
            & r2_hidden(X3,sK0)
            & r2_hidden(X2,sK0) )
        | ~ v2_funct_1(sK1) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
            | ~ r2_hidden(X5,sK0)
            | ~ r2_hidden(X4,sK0) )
        | v2_funct_1(sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK2 != sK3
        & k1_funct_1(X1,sK2) = k1_funct_1(X1,sK3)
        & r2_hidden(sK3,X0)
        & r2_hidden(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',t77_funct_2)).

fof(f219,plain,
    ( sK2 = sK3
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f216,f91])).

fof(f91,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f216,plain,
    ( ~ r2_hidden(sK2,sK0)
    | sK2 = sK3
    | ~ spl7_0 ),
    inference(equality_resolution,[],[f204])).

fof(f204,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | ~ r2_hidden(X0,sK0)
        | sK3 = X0 )
    | ~ spl7_0 ),
    inference(forward_demodulation,[],[f203,f121])).

fof(f121,plain,(
    k1_relat_1(sK1) = sK0 ),
    inference(forward_demodulation,[],[f110,f115])).

fof(f115,plain,(
    k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unit_resulting_resolution,[],[f55,f56,f57,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',t67_funct_2)).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f56,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f55,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f110,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f57,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',redefinition_k1_relset_1)).

fof(f203,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f202,f188])).

fof(f188,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f60,f82])).

fof(f60,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,sK0)
        | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_0 ),
    inference(forward_demodulation,[],[f201,f121])).

fof(f201,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f200,f96])).

fof(f96,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f57,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',cc1_relset_1)).

fof(f200,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f199,f55])).

fof(f199,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f197,f82])).

fof(f197,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
        | sK3 = X0
        | ~ r2_hidden(sK3,k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_0 ),
    inference(superposition,[],[f64,f196])).

fof(f196,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_0 ),
    inference(subsumption_resolution,[],[f61,f82])).

fof(f61,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f64,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t77_funct_2.p',d8_funct_1)).

fof(f178,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f153,f105])).

fof(f105,plain,
    ( sK4(sK1) != sK5(sK1)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f96,f55,f85,f68])).

fof(f68,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,
    ( ~ v2_funct_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_1
  <=> ~ v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f153,plain,
    ( sK4(sK1) = sK5(sK1)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f127,f125,f114,f93])).

fof(f93,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
        | X4 = X5
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f58,f85])).

fof(f58,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK1,X4) != k1_funct_1(sK1,X5)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X4,sK0)
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f114,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f85,f55,f96,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f125,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f121,f103])).

fof(f103,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f85,f55,f96,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f127,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f121,f98])).

fof(f98,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f85,f55,f96,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f59,f90,f84])).

fof(f59,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
