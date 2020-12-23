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
% DateTime   : Thu Dec  3 13:01:25 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 826 expanded)
%              Number of leaves         :   18 ( 222 expanded)
%              Depth                    :   21
%              Number of atoms          :  603 (7288 expanded)
%              Number of equality atoms :  188 (2835 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f82,f91,f125,f130,f157,f172,f254])).

fof(f254,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f252,f67])).

fof(f67,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl7_3
  <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f252,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK4)
    | ~ spl7_1
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f250,f62])).

fof(f62,plain,
    ( sK3 != sK4
    | spl7_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_2
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f250,plain,
    ( sK3 = sK4
    | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK4)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(resolution,[],[f248,f72])).

fof(f72,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_4
  <=> r2_hidden(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f248,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | sK3 = X1
        | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X1) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(resolution,[],[f246,f77])).

fof(f77,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_5
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
        | X0 = X1
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f245,f93])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f92,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f92,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f36,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ( sK3 != sK4
        & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
        & r2_hidden(sK4,sK0)
        & r2_hidden(sK3,sK0) )
      | ~ v2_funct_1(sK2) )
    & ( ! [X5,X6] :
          ( X5 = X6
          | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
          | ~ r2_hidden(X6,sK0)
          | ~ r2_hidden(X5,sK0) )
      | v2_funct_1(sK2) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) )
          | ~ v2_funct_1(X2) )
        & ( ! [X5,X6] :
              ( X5 = X6
              | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
              | ~ r2_hidden(X6,X0)
              | ~ r2_hidden(X5,X0) )
          | v2_funct_1(X2) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ? [X4,X3] :
            ( X3 != X4
            & k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4)
            & r2_hidden(X4,sK0)
            & r2_hidden(X3,sK0) )
        | ~ v2_funct_1(sK2) )
      & ( ! [X6,X5] :
            ( X5 = X6
            | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
            | ~ r2_hidden(X6,sK0)
            | ~ r2_hidden(X5,sK0) )
        | v2_funct_1(sK2) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X4,X3] :
        ( X3 != X4
        & k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4)
        & r2_hidden(X4,sK0)
        & r2_hidden(X3,sK0) )
   => ( sK3 != sK4
      & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
      & r2_hidden(sK4,sK0)
      & r2_hidden(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X5,X6] :
            ( X5 = X6
            | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
            | ~ r2_hidden(X6,X0)
            | ~ r2_hidden(X5,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) )
        | ~ v2_funct_1(X2) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | v2_funct_1(X2) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <~> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v2_funct_1(X2)
          <=> ! [X3,X4] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  & r2_hidden(X4,X0)
                  & r2_hidden(X3,X0) )
               => X3 = X4 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
        | X0 = X1
        | ~ r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f244,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
        | X0 = X1
        | ~ r2_hidden(X1,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f243,f57])).

fof(f57,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)
        | X0 = X1
        | ~ r2_hidden(X1,sK0)
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_9 ),
    inference(superposition,[],[f37,f241])).

fof(f241,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(superposition,[],[f129,f103])).

fof(f103,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f43,f29])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f129,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f37,plain,(
    ! [X4,X0,X3] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK5(X0) != sK6(X0)
            & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
            & r2_hidden(sK6(X0),k1_relat_1(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK5(X0) != sK6(X0)
        & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f172,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f170,f102])).

fof(f102,plain,
    ( sK5(sK2) != sK6(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f101,f93])).

fof(f101,plain,
    ( sK5(sK2) != sK6(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f100,f58])).

fof(f58,plain,
    ( ~ v2_funct_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f100,plain,
    ( sK5(sK2) != sK6(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f41,f27])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sK5(X0) != sK6(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f170,plain,
    ( sK5(sK2) = sK6(sK2)
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( sK5(sK2) = sK6(sK2)
    | k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK5(sK2))
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(resolution,[],[f166,f163])).

fof(f163,plain,
    ( r2_hidden(sK5(sK2),k1_xboole_0)
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f96,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f136,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f148,f138])).

fof(f138,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f135,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f135,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_7 ),
    inference(superposition,[],[f28,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f28,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f148,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(resolution,[],[f137,f54])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f137,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f134,f90])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_7 ),
    inference(superposition,[],[f29,f85])).

fof(f136,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f133,f90])).

fof(f133,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl7_7 ),
    inference(superposition,[],[f103,f85])).

fof(f96,plain,
    ( r2_hidden(sK5(sK2),k1_relat_1(sK2))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f95,f93])).

fof(f95,plain,
    ( r2_hidden(sK5(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f94,f58])).

fof(f94,plain,
    ( r2_hidden(sK5(sK2),k1_relat_1(sK2))
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f38,f27])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | sK6(sK2) = X0
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2)) )
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f165,f106])).

fof(f106,plain,
    ( k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f105,f93])).

fof(f105,plain,
    ( k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2))
    | ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f104,f58])).

fof(f104,plain,
    ( k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2))
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f40,f27])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f165,plain,
    ( ! [X0] :
        ( sK6(sK2) = X0
        | ~ r2_hidden(X0,k1_xboole_0)
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK6(sK2)) )
    | spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(resolution,[],[f162,f143])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | X0 = X1
        | ~ r2_hidden(X1,k1_xboole_0)
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1) )
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(superposition,[],[f81,f90])).

fof(f81,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,sK0)
        | X5 = X6
        | ~ r2_hidden(X6,sK0)
        | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl7_6
  <=> ! [X5,X6] :
        ( X5 = X6
        | ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X6,sK0)
        | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f162,plain,
    ( r2_hidden(sK6(sK2),k1_xboole_0)
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f99,f160])).

fof(f99,plain,
    ( r2_hidden(sK6(sK2),k1_relat_1(sK2))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f98,f93])).

fof(f98,plain,
    ( r2_hidden(sK6(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f97,f58])).

fof(f97,plain,
    ( r2_hidden(sK6(sK2),k1_relat_1(sK2))
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f39,f27])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f157,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9 ),
    inference(subsumption_resolution,[],[f155,f132])).

fof(f132,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9 ),
    inference(forward_demodulation,[],[f131,f90])).

fof(f131,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl7_7
    | spl7_9 ),
    inference(forward_demodulation,[],[f128,f85])).

fof(f128,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f130,plain,
    ( spl7_9
    | spl7_7 ),
    inference(avatar_split_clause,[],[f108,f84,f127])).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f107,f28])).

fof(f107,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f125,plain,
    ( spl7_1
    | ~ spl7_6
    | spl7_7 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | spl7_7 ),
    inference(subsumption_resolution,[],[f123,f102])).

fof(f123,plain,
    ( sK5(sK2) = sK6(sK2)
    | spl7_1
    | ~ spl7_6
    | spl7_7 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( sK5(sK2) = sK6(sK2)
    | k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK5(sK2))
    | spl7_1
    | ~ spl7_6
    | spl7_7 ),
    inference(resolution,[],[f119,f116])).

fof(f116,plain,
    ( r2_hidden(sK5(sK2),sK0)
    | spl7_1
    | spl7_7 ),
    inference(superposition,[],[f96,f113])).

fof(f113,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl7_7 ),
    inference(superposition,[],[f103,f109])).

fof(f109,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f108,f86])).

fof(f86,plain,
    ( k1_xboole_0 != sK1
    | spl7_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sK6(sK2) = X0
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2)) )
    | spl7_1
    | ~ spl7_6
    | spl7_7 ),
    inference(forward_demodulation,[],[f118,f106])).

fof(f118,plain,
    ( ! [X0] :
        ( sK6(sK2) = X0
        | ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK6(sK2)) )
    | spl7_1
    | ~ spl7_6
    | spl7_7 ),
    inference(resolution,[],[f115,f81])).

fof(f115,plain,
    ( r2_hidden(sK6(sK2),sK0)
    | spl7_1
    | spl7_7 ),
    inference(superposition,[],[f99,f113])).

fof(f91,plain,
    ( ~ spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f30,f88,f84])).

fof(f30,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f31,f80,f56])).

fof(f31,plain,(
    ! [X6,X5] :
      ( X5 = X6
      | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
      | ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X5,sK0)
      | v2_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f32,f75,f56])).

fof(f32,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f33,f70,f56])).

fof(f33,plain,
    ( r2_hidden(sK4,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f34,f65,f56])).

fof(f34,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f35,f60,f56])).

fof(f35,plain,
    ( sK3 != sK4
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (1226670080)
% 0.13/0.36  ipcrm: permission denied for id (1226735618)
% 0.13/0.37  ipcrm: permission denied for id (1226866695)
% 0.13/0.37  ipcrm: permission denied for id (1226932233)
% 0.13/0.37  ipcrm: permission denied for id (1231028234)
% 0.13/0.37  ipcrm: permission denied for id (1231061003)
% 0.13/0.38  ipcrm: permission denied for id (1227030540)
% 0.13/0.38  ipcrm: permission denied for id (1227063309)
% 0.13/0.38  ipcrm: permission denied for id (1227096078)
% 0.13/0.38  ipcrm: permission denied for id (1231093775)
% 0.13/0.38  ipcrm: permission denied for id (1231126544)
% 0.13/0.38  ipcrm: permission denied for id (1227194385)
% 0.13/0.38  ipcrm: permission denied for id (1231159314)
% 0.13/0.38  ipcrm: permission denied for id (1227259923)
% 0.13/0.39  ipcrm: permission denied for id (1231224853)
% 0.13/0.39  ipcrm: permission denied for id (1231257622)
% 0.13/0.39  ipcrm: permission denied for id (1227423768)
% 0.13/0.39  ipcrm: permission denied for id (1231421468)
% 0.13/0.40  ipcrm: permission denied for id (1227587613)
% 0.13/0.40  ipcrm: permission denied for id (1227620382)
% 0.21/0.40  ipcrm: permission denied for id (1227685920)
% 0.21/0.40  ipcrm: permission denied for id (1227784227)
% 0.21/0.40  ipcrm: permission denied for id (1231552548)
% 0.21/0.41  ipcrm: permission denied for id (1227849765)
% 0.21/0.41  ipcrm: permission denied for id (1227882534)
% 0.21/0.41  ipcrm: permission denied for id (1227948072)
% 0.21/0.41  ipcrm: permission denied for id (1227980841)
% 0.21/0.41  ipcrm: permission denied for id (1231618090)
% 0.21/0.41  ipcrm: permission denied for id (1228046379)
% 0.21/0.41  ipcrm: permission denied for id (1228079148)
% 0.21/0.41  ipcrm: permission denied for id (1228111917)
% 0.21/0.42  ipcrm: permission denied for id (1231650862)
% 0.21/0.42  ipcrm: permission denied for id (1228210223)
% 0.21/0.42  ipcrm: permission denied for id (1228242992)
% 0.21/0.42  ipcrm: permission denied for id (1228275761)
% 0.21/0.42  ipcrm: permission denied for id (1228308530)
% 0.21/0.42  ipcrm: permission denied for id (1231716404)
% 0.21/0.42  ipcrm: permission denied for id (1231749173)
% 0.21/0.43  ipcrm: permission denied for id (1228439606)
% 0.21/0.43  ipcrm: permission denied for id (1228505144)
% 0.21/0.43  ipcrm: permission denied for id (1231814713)
% 0.21/0.43  ipcrm: permission denied for id (1228570682)
% 0.21/0.43  ipcrm: permission denied for id (1228603451)
% 0.21/0.43  ipcrm: permission denied for id (1228636220)
% 0.21/0.43  ipcrm: permission denied for id (1228668989)
% 0.21/0.43  ipcrm: permission denied for id (1228701758)
% 0.21/0.44  ipcrm: permission denied for id (1228767296)
% 0.21/0.44  ipcrm: permission denied for id (1228800065)
% 0.21/0.44  ipcrm: permission denied for id (1228832834)
% 0.21/0.44  ipcrm: permission denied for id (1231880259)
% 0.21/0.44  ipcrm: permission denied for id (1231913028)
% 0.21/0.44  ipcrm: permission denied for id (1228931141)
% 0.21/0.44  ipcrm: permission denied for id (1231945798)
% 0.21/0.45  ipcrm: permission denied for id (1231978567)
% 0.21/0.45  ipcrm: permission denied for id (1229029448)
% 0.21/0.45  ipcrm: permission denied for id (1232011337)
% 0.21/0.45  ipcrm: permission denied for id (1229094986)
% 0.21/0.45  ipcrm: permission denied for id (1229127755)
% 0.21/0.45  ipcrm: permission denied for id (1232044108)
% 0.21/0.45  ipcrm: permission denied for id (1229193293)
% 0.21/0.45  ipcrm: permission denied for id (1232109647)
% 0.21/0.46  ipcrm: permission denied for id (1232142416)
% 0.21/0.46  ipcrm: permission denied for id (1229324369)
% 0.21/0.46  ipcrm: permission denied for id (1232175186)
% 0.21/0.46  ipcrm: permission denied for id (1229389907)
% 0.21/0.46  ipcrm: permission denied for id (1232207956)
% 0.21/0.46  ipcrm: permission denied for id (1232273494)
% 0.21/0.46  ipcrm: permission denied for id (1229520983)
% 0.21/0.46  ipcrm: permission denied for id (1232306264)
% 0.21/0.47  ipcrm: permission denied for id (1229586521)
% 0.21/0.47  ipcrm: permission denied for id (1229619290)
% 0.21/0.47  ipcrm: permission denied for id (1232339035)
% 0.21/0.47  ipcrm: permission denied for id (1232437342)
% 0.21/0.47  ipcrm: permission denied for id (1229783135)
% 0.21/0.47  ipcrm: permission denied for id (1229815904)
% 0.21/0.48  ipcrm: permission denied for id (1232470113)
% 0.21/0.48  ipcrm: permission denied for id (1232502882)
% 0.21/0.48  ipcrm: permission denied for id (1229914211)
% 0.21/0.48  ipcrm: permission denied for id (1232535652)
% 0.21/0.48  ipcrm: permission denied for id (1229946981)
% 0.21/0.48  ipcrm: permission denied for id (1229979750)
% 0.21/0.48  ipcrm: permission denied for id (1230012519)
% 0.21/0.48  ipcrm: permission denied for id (1230045288)
% 0.21/0.48  ipcrm: permission denied for id (1230078057)
% 0.21/0.49  ipcrm: permission denied for id (1232601195)
% 0.21/0.49  ipcrm: permission denied for id (1230176364)
% 0.21/0.49  ipcrm: permission denied for id (1230241902)
% 0.21/0.49  ipcrm: permission denied for id (1230307440)
% 0.21/0.50  ipcrm: permission denied for id (1230405747)
% 0.21/0.50  ipcrm: permission denied for id (1232765044)
% 0.21/0.50  ipcrm: permission denied for id (1230504054)
% 0.21/0.50  ipcrm: permission denied for id (1232928890)
% 0.21/0.51  ipcrm: permission denied for id (1230667899)
% 0.21/0.51  ipcrm: permission denied for id (1232961660)
% 0.21/0.51  ipcrm: permission denied for id (1230733437)
% 0.21/0.51  ipcrm: permission denied for id (1230798975)
% 0.92/0.62  % (24383)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.92/0.62  % (24385)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.09/0.63  % (24377)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.09/0.63  % (24399)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.10/0.65  % (24386)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.10/0.65  % (24392)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.10/0.65  % (24385)Refutation found. Thanks to Tanya!
% 1.10/0.65  % SZS status Theorem for theBenchmark
% 1.10/0.65  % SZS output start Proof for theBenchmark
% 1.10/0.65  fof(f255,plain,(
% 1.10/0.65    $false),
% 1.10/0.65    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f82,f91,f125,f130,f157,f172,f254])).
% 1.10/0.65  fof(f254,plain,(
% 1.10/0.65    ~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_9),
% 1.10/0.65    inference(avatar_contradiction_clause,[],[f253])).
% 1.10/0.65  fof(f253,plain,(
% 1.10/0.65    $false | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_9)),
% 1.10/0.65    inference(subsumption_resolution,[],[f252,f67])).
% 1.10/0.65  fof(f67,plain,(
% 1.10/0.65    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~spl7_3),
% 1.10/0.65    inference(avatar_component_clause,[],[f65])).
% 1.10/0.65  fof(f65,plain,(
% 1.10/0.65    spl7_3 <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.10/0.65  fof(f252,plain,(
% 1.10/0.65    k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK4) | (~spl7_1 | spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_9)),
% 1.10/0.65    inference(subsumption_resolution,[],[f250,f62])).
% 1.10/0.65  fof(f62,plain,(
% 1.10/0.65    sK3 != sK4 | spl7_2),
% 1.10/0.65    inference(avatar_component_clause,[],[f60])).
% 1.10/0.65  fof(f60,plain,(
% 1.10/0.65    spl7_2 <=> sK3 = sK4),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.10/0.65  fof(f250,plain,(
% 1.10/0.65    sK3 = sK4 | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK4) | (~spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_9)),
% 1.10/0.65    inference(resolution,[],[f248,f72])).
% 1.10/0.65  fof(f72,plain,(
% 1.10/0.65    r2_hidden(sK4,sK0) | ~spl7_4),
% 1.10/0.65    inference(avatar_component_clause,[],[f70])).
% 1.10/0.65  fof(f70,plain,(
% 1.10/0.65    spl7_4 <=> r2_hidden(sK4,sK0)),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.10/0.65  fof(f248,plain,(
% 1.10/0.65    ( ! [X1] : (~r2_hidden(X1,sK0) | sK3 = X1 | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X1)) ) | (~spl7_1 | ~spl7_5 | ~spl7_9)),
% 1.10/0.65    inference(resolution,[],[f246,f77])).
% 1.10/0.65  fof(f77,plain,(
% 1.10/0.65    r2_hidden(sK3,sK0) | ~spl7_5),
% 1.10/0.65    inference(avatar_component_clause,[],[f75])).
% 1.10/0.65  fof(f75,plain,(
% 1.10/0.65    spl7_5 <=> r2_hidden(sK3,sK0)),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.10/0.65  fof(f246,plain,(
% 1.10/0.65    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1) | X0 = X1 | ~r2_hidden(X1,sK0)) ) | (~spl7_1 | ~spl7_9)),
% 1.10/0.65    inference(subsumption_resolution,[],[f245,f93])).
% 1.10/0.65  fof(f93,plain,(
% 1.10/0.65    v1_relat_1(sK2)),
% 1.10/0.65    inference(subsumption_resolution,[],[f92,f42])).
% 1.10/0.65  fof(f42,plain,(
% 1.10/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.10/0.65    inference(cnf_transformation,[],[f2])).
% 1.10/0.65  fof(f2,axiom,(
% 1.10/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.10/0.65  fof(f92,plain,(
% 1.10/0.65    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.10/0.65    inference(resolution,[],[f36,f29])).
% 1.10/0.65  fof(f29,plain,(
% 1.10/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  fof(f21,plain,(
% 1.10/0.65    ((sK3 != sK4 & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) & r2_hidden(sK4,sK0) & r2_hidden(sK3,sK0)) | ~v2_funct_1(sK2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | ~r2_hidden(X6,sK0) | ~r2_hidden(X5,sK0)) | v2_funct_1(sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f20,f19])).
% 1.10/0.65  fof(f19,plain,(
% 1.10/0.65    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((? [X4,X3] : (X3 != X4 & k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4) & r2_hidden(X4,sK0) & r2_hidden(X3,sK0)) | ~v2_funct_1(sK2)) & (! [X6,X5] : (X5 = X6 | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | ~r2_hidden(X6,sK0) | ~r2_hidden(X5,sK0)) | v2_funct_1(sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.10/0.65    introduced(choice_axiom,[])).
% 1.10/0.65  fof(f20,plain,(
% 1.10/0.65    ? [X4,X3] : (X3 != X4 & k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4) & r2_hidden(X4,sK0) & r2_hidden(X3,sK0)) => (sK3 != sK4 & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) & r2_hidden(sK4,sK0) & r2_hidden(sK3,sK0))),
% 1.10/0.65    introduced(choice_axiom,[])).
% 1.10/0.65  fof(f18,plain,(
% 1.10/0.65    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.10/0.65    inference(rectify,[],[f17])).
% 1.10/0.65  fof(f17,plain,(
% 1.10/0.65    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.10/0.65    inference(flattening,[],[f16])).
% 1.10/0.65  fof(f16,plain,(
% 1.10/0.65    ? [X0,X1,X2] : (((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | v2_funct_1(X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.10/0.65    inference(nnf_transformation,[],[f9])).
% 1.10/0.65  fof(f9,plain,(
% 1.10/0.65    ? [X0,X1,X2] : ((v2_funct_1(X2) <~> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.10/0.65    inference(flattening,[],[f8])).
% 1.10/0.65  fof(f8,plain,(
% 1.10/0.65    ? [X0,X1,X2] : (((v2_funct_1(X2) <~> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.10/0.65    inference(ennf_transformation,[],[f7])).
% 1.10/0.65  fof(f7,negated_conjecture,(
% 1.10/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 1.10/0.65    inference(negated_conjecture,[],[f6])).
% 1.10/0.65  fof(f6,conjecture,(
% 1.10/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 1.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).
% 1.10/0.65  fof(f36,plain,(
% 1.10/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.10/0.65    inference(cnf_transformation,[],[f10])).
% 1.10/0.65  fof(f10,plain,(
% 1.10/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.10/0.65    inference(ennf_transformation,[],[f1])).
% 1.10/0.65  fof(f1,axiom,(
% 1.10/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.10/0.65  fof(f245,plain,(
% 1.10/0.65    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1) | X0 = X1 | ~r2_hidden(X1,sK0) | ~v1_relat_1(sK2)) ) | (~spl7_1 | ~spl7_9)),
% 1.10/0.65    inference(subsumption_resolution,[],[f244,f27])).
% 1.10/0.65  fof(f27,plain,(
% 1.10/0.65    v1_funct_1(sK2)),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  fof(f244,plain,(
% 1.10/0.65    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1) | X0 = X1 | ~r2_hidden(X1,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl7_1 | ~spl7_9)),
% 1.10/0.65    inference(subsumption_resolution,[],[f243,f57])).
% 1.10/0.65  fof(f57,plain,(
% 1.10/0.65    v2_funct_1(sK2) | ~spl7_1),
% 1.10/0.65    inference(avatar_component_clause,[],[f56])).
% 1.10/0.65  fof(f56,plain,(
% 1.10/0.65    spl7_1 <=> v2_funct_1(sK2)),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.10/0.65  fof(f243,plain,(
% 1.10/0.65    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1) | X0 = X1 | ~r2_hidden(X1,sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_9),
% 1.10/0.65    inference(superposition,[],[f37,f241])).
% 1.10/0.65  fof(f241,plain,(
% 1.10/0.65    sK0 = k1_relat_1(sK2) | ~spl7_9),
% 1.10/0.65    inference(superposition,[],[f129,f103])).
% 1.10/0.65  fof(f103,plain,(
% 1.10/0.65    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.10/0.65    inference(resolution,[],[f43,f29])).
% 1.10/0.65  fof(f43,plain,(
% 1.10/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.10/0.65    inference(cnf_transformation,[],[f13])).
% 1.10/0.65  fof(f13,plain,(
% 1.10/0.65    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.10/0.65    inference(ennf_transformation,[],[f4])).
% 1.10/0.65  fof(f4,axiom,(
% 1.10/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.10/0.65  fof(f129,plain,(
% 1.10/0.65    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_9),
% 1.10/0.65    inference(avatar_component_clause,[],[f127])).
% 1.10/0.65  fof(f127,plain,(
% 1.10/0.65    spl7_9 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.10/0.65  fof(f37,plain,(
% 1.10/0.65    ( ! [X4,X0,X3] : (~r2_hidden(X4,k1_relat_1(X0)) | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.10/0.65    inference(cnf_transformation,[],[f25])).
% 1.10/0.65  fof(f25,plain,(
% 1.10/0.65    ! [X0] : (((v2_funct_1(X0) | (sK5(X0) != sK6(X0) & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f23,f24])).
% 1.10/0.65  fof(f24,plain,(
% 1.10/0.65    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK5(X0) != sK6(X0) & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0))))),
% 1.10/0.65    introduced(choice_axiom,[])).
% 1.10/0.65  fof(f23,plain,(
% 1.10/0.65    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.10/0.65    inference(rectify,[],[f22])).
% 1.10/0.65  fof(f22,plain,(
% 1.10/0.65    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.10/0.65    inference(nnf_transformation,[],[f12])).
% 1.10/0.65  fof(f12,plain,(
% 1.10/0.65    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.10/0.65    inference(flattening,[],[f11])).
% 1.10/0.65  fof(f11,plain,(
% 1.10/0.65    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.10/0.65    inference(ennf_transformation,[],[f3])).
% 1.10/0.65  fof(f3,axiom,(
% 1.10/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 1.10/0.65  fof(f172,plain,(
% 1.10/0.65    spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8),
% 1.10/0.65    inference(avatar_contradiction_clause,[],[f171])).
% 1.10/0.65  fof(f171,plain,(
% 1.10/0.65    $false | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(subsumption_resolution,[],[f170,f102])).
% 1.10/0.65  fof(f102,plain,(
% 1.10/0.65    sK5(sK2) != sK6(sK2) | spl7_1),
% 1.10/0.65    inference(subsumption_resolution,[],[f101,f93])).
% 1.10/0.65  fof(f101,plain,(
% 1.10/0.65    sK5(sK2) != sK6(sK2) | ~v1_relat_1(sK2) | spl7_1),
% 1.10/0.65    inference(subsumption_resolution,[],[f100,f58])).
% 1.10/0.65  fof(f58,plain,(
% 1.10/0.65    ~v2_funct_1(sK2) | spl7_1),
% 1.10/0.65    inference(avatar_component_clause,[],[f56])).
% 1.10/0.65  fof(f100,plain,(
% 1.10/0.65    sK5(sK2) != sK6(sK2) | v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.10/0.65    inference(resolution,[],[f41,f27])).
% 1.10/0.65  fof(f41,plain,(
% 1.10/0.65    ( ! [X0] : (~v1_funct_1(X0) | sK5(X0) != sK6(X0) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.10/0.65    inference(cnf_transformation,[],[f25])).
% 1.10/0.65  fof(f170,plain,(
% 1.10/0.65    sK5(sK2) = sK6(sK2) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(trivial_inequality_removal,[],[f169])).
% 1.10/0.65  fof(f169,plain,(
% 1.10/0.65    sK5(sK2) = sK6(sK2) | k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK5(sK2)) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(resolution,[],[f166,f163])).
% 1.10/0.65  fof(f163,plain,(
% 1.10/0.65    r2_hidden(sK5(sK2),k1_xboole_0) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(superposition,[],[f96,f160])).
% 1.10/0.65  fof(f160,plain,(
% 1.10/0.65    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(superposition,[],[f136,f155])).
% 1.10/0.65  fof(f155,plain,(
% 1.10/0.65    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(subsumption_resolution,[],[f148,f138])).
% 1.10/0.65  fof(f138,plain,(
% 1.10/0.65    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(forward_demodulation,[],[f135,f90])).
% 1.10/0.65  fof(f90,plain,(
% 1.10/0.65    k1_xboole_0 = sK0 | ~spl7_8),
% 1.10/0.65    inference(avatar_component_clause,[],[f88])).
% 1.10/0.65  fof(f88,plain,(
% 1.10/0.65    spl7_8 <=> k1_xboole_0 = sK0),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.10/0.65  fof(f135,plain,(
% 1.10/0.65    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_7),
% 1.10/0.65    inference(superposition,[],[f28,f85])).
% 1.10/0.65  fof(f85,plain,(
% 1.10/0.65    k1_xboole_0 = sK1 | ~spl7_7),
% 1.10/0.65    inference(avatar_component_clause,[],[f84])).
% 1.10/0.65  fof(f84,plain,(
% 1.10/0.65    spl7_7 <=> k1_xboole_0 = sK1),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.10/0.65  fof(f28,plain,(
% 1.10/0.65    v1_funct_2(sK2,sK0,sK1)),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  fof(f148,plain,(
% 1.10/0.65    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(resolution,[],[f137,f54])).
% 1.10/0.65  fof(f54,plain,(
% 1.10/0.65    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.10/0.65    inference(equality_resolution,[],[f45])).
% 1.10/0.65  fof(f45,plain,(
% 1.10/0.65    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.10/0.65    inference(cnf_transformation,[],[f26])).
% 1.10/0.65  fof(f26,plain,(
% 1.10/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.10/0.65    inference(nnf_transformation,[],[f15])).
% 1.10/0.65  fof(f15,plain,(
% 1.10/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.10/0.65    inference(flattening,[],[f14])).
% 1.10/0.65  fof(f14,plain,(
% 1.10/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.10/0.65    inference(ennf_transformation,[],[f5])).
% 1.10/0.65  fof(f5,axiom,(
% 1.10/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.10/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.10/0.65  fof(f137,plain,(
% 1.10/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(forward_demodulation,[],[f134,f90])).
% 1.10/0.65  fof(f134,plain,(
% 1.10/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_7),
% 1.10/0.65    inference(superposition,[],[f29,f85])).
% 1.10/0.65  fof(f136,plain,(
% 1.10/0.65    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(forward_demodulation,[],[f133,f90])).
% 1.10/0.65  fof(f133,plain,(
% 1.10/0.65    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl7_7),
% 1.10/0.65    inference(superposition,[],[f103,f85])).
% 1.10/0.65  fof(f96,plain,(
% 1.10/0.65    r2_hidden(sK5(sK2),k1_relat_1(sK2)) | spl7_1),
% 1.10/0.65    inference(subsumption_resolution,[],[f95,f93])).
% 1.10/0.65  fof(f95,plain,(
% 1.10/0.65    r2_hidden(sK5(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl7_1),
% 1.10/0.65    inference(subsumption_resolution,[],[f94,f58])).
% 1.10/0.65  fof(f94,plain,(
% 1.10/0.65    r2_hidden(sK5(sK2),k1_relat_1(sK2)) | v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.10/0.65    inference(resolution,[],[f38,f27])).
% 1.10/0.65  fof(f38,plain,(
% 1.10/0.65    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.10/0.65    inference(cnf_transformation,[],[f25])).
% 1.10/0.65  fof(f166,plain,(
% 1.10/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK6(sK2) = X0 | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2))) ) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(forward_demodulation,[],[f165,f106])).
% 1.10/0.65  fof(f106,plain,(
% 1.10/0.65    k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2)) | spl7_1),
% 1.10/0.65    inference(subsumption_resolution,[],[f105,f93])).
% 1.10/0.65  fof(f105,plain,(
% 1.10/0.65    k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2)) | ~v1_relat_1(sK2) | spl7_1),
% 1.10/0.65    inference(subsumption_resolution,[],[f104,f58])).
% 1.10/0.65  fof(f104,plain,(
% 1.10/0.65    k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2)) | v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.10/0.65    inference(resolution,[],[f40,f27])).
% 1.10/0.65  fof(f40,plain,(
% 1.10/0.65    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.10/0.65    inference(cnf_transformation,[],[f25])).
% 1.10/0.65  fof(f165,plain,(
% 1.10/0.65    ( ! [X0] : (sK6(sK2) = X0 | ~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK6(sK2))) ) | (spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(resolution,[],[f162,f143])).
% 1.10/0.65  fof(f143,plain,(
% 1.10/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | X0 = X1 | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK2,X0) != k1_funct_1(sK2,X1)) ) | (~spl7_6 | ~spl7_8)),
% 1.10/0.65    inference(superposition,[],[f81,f90])).
% 1.10/0.65  fof(f81,plain,(
% 1.10/0.65    ( ! [X6,X5] : (~r2_hidden(X5,sK0) | X5 = X6 | ~r2_hidden(X6,sK0) | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)) ) | ~spl7_6),
% 1.10/0.65    inference(avatar_component_clause,[],[f80])).
% 1.10/0.65  fof(f80,plain,(
% 1.10/0.65    spl7_6 <=> ! [X5,X6] : (X5 = X6 | ~r2_hidden(X5,sK0) | ~r2_hidden(X6,sK0) | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6))),
% 1.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.10/0.65  fof(f162,plain,(
% 1.10/0.65    r2_hidden(sK6(sK2),k1_xboole_0) | (spl7_1 | ~spl7_7 | ~spl7_8)),
% 1.10/0.65    inference(superposition,[],[f99,f160])).
% 1.10/0.65  fof(f99,plain,(
% 1.10/0.65    r2_hidden(sK6(sK2),k1_relat_1(sK2)) | spl7_1),
% 1.10/0.65    inference(subsumption_resolution,[],[f98,f93])).
% 1.10/0.65  fof(f98,plain,(
% 1.10/0.65    r2_hidden(sK6(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl7_1),
% 1.10/0.65    inference(subsumption_resolution,[],[f97,f58])).
% 1.10/0.65  fof(f97,plain,(
% 1.10/0.65    r2_hidden(sK6(sK2),k1_relat_1(sK2)) | v2_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.10/0.65    inference(resolution,[],[f39,f27])).
% 1.10/0.65  fof(f39,plain,(
% 1.10/0.65    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK6(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.10/0.65    inference(cnf_transformation,[],[f25])).
% 1.10/0.65  fof(f157,plain,(
% 1.10/0.65    ~spl7_7 | ~spl7_8 | spl7_9),
% 1.10/0.65    inference(avatar_contradiction_clause,[],[f156])).
% 1.10/0.65  fof(f156,plain,(
% 1.10/0.65    $false | (~spl7_7 | ~spl7_8 | spl7_9)),
% 1.10/0.65    inference(subsumption_resolution,[],[f155,f132])).
% 1.10/0.65  fof(f132,plain,(
% 1.10/0.65    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_7 | ~spl7_8 | spl7_9)),
% 1.10/0.65    inference(forward_demodulation,[],[f131,f90])).
% 1.10/0.65  fof(f131,plain,(
% 1.10/0.65    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (~spl7_7 | spl7_9)),
% 1.10/0.65    inference(forward_demodulation,[],[f128,f85])).
% 1.10/0.65  fof(f128,plain,(
% 1.10/0.65    sK0 != k1_relset_1(sK0,sK1,sK2) | spl7_9),
% 1.10/0.65    inference(avatar_component_clause,[],[f127])).
% 1.10/0.65  fof(f130,plain,(
% 1.10/0.65    spl7_9 | spl7_7),
% 1.10/0.65    inference(avatar_split_clause,[],[f108,f84,f127])).
% 1.10/0.65  fof(f108,plain,(
% 1.10/0.65    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.10/0.65    inference(subsumption_resolution,[],[f107,f28])).
% 1.10/0.65  fof(f107,plain,(
% 1.10/0.65    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.10/0.65    inference(resolution,[],[f44,f29])).
% 1.10/0.65  fof(f44,plain,(
% 1.10/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.10/0.65    inference(cnf_transformation,[],[f26])).
% 1.10/0.65  fof(f125,plain,(
% 1.10/0.65    spl7_1 | ~spl7_6 | spl7_7),
% 1.10/0.65    inference(avatar_contradiction_clause,[],[f124])).
% 1.10/0.65  fof(f124,plain,(
% 1.10/0.65    $false | (spl7_1 | ~spl7_6 | spl7_7)),
% 1.10/0.65    inference(subsumption_resolution,[],[f123,f102])).
% 1.10/0.65  fof(f123,plain,(
% 1.10/0.65    sK5(sK2) = sK6(sK2) | (spl7_1 | ~spl7_6 | spl7_7)),
% 1.10/0.65    inference(trivial_inequality_removal,[],[f122])).
% 1.10/0.65  fof(f122,plain,(
% 1.10/0.65    sK5(sK2) = sK6(sK2) | k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK5(sK2)) | (spl7_1 | ~spl7_6 | spl7_7)),
% 1.10/0.65    inference(resolution,[],[f119,f116])).
% 1.10/0.65  fof(f116,plain,(
% 1.10/0.65    r2_hidden(sK5(sK2),sK0) | (spl7_1 | spl7_7)),
% 1.10/0.65    inference(superposition,[],[f96,f113])).
% 1.10/0.65  fof(f113,plain,(
% 1.10/0.65    sK0 = k1_relat_1(sK2) | spl7_7),
% 1.10/0.65    inference(superposition,[],[f103,f109])).
% 1.10/0.65  fof(f109,plain,(
% 1.10/0.65    sK0 = k1_relset_1(sK0,sK1,sK2) | spl7_7),
% 1.10/0.65    inference(subsumption_resolution,[],[f108,f86])).
% 1.10/0.65  fof(f86,plain,(
% 1.10/0.65    k1_xboole_0 != sK1 | spl7_7),
% 1.10/0.65    inference(avatar_component_clause,[],[f84])).
% 1.10/0.65  fof(f119,plain,(
% 1.10/0.65    ( ! [X0] : (~r2_hidden(X0,sK0) | sK6(sK2) = X0 | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK5(sK2))) ) | (spl7_1 | ~spl7_6 | spl7_7)),
% 1.10/0.65    inference(forward_demodulation,[],[f118,f106])).
% 1.10/0.65  fof(f118,plain,(
% 1.10/0.65    ( ! [X0] : (sK6(sK2) = X0 | ~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) != k1_funct_1(sK2,sK6(sK2))) ) | (spl7_1 | ~spl7_6 | spl7_7)),
% 1.10/0.65    inference(resolution,[],[f115,f81])).
% 1.10/0.65  fof(f115,plain,(
% 1.10/0.65    r2_hidden(sK6(sK2),sK0) | (spl7_1 | spl7_7)),
% 1.10/0.65    inference(superposition,[],[f99,f113])).
% 1.10/0.65  fof(f91,plain,(
% 1.10/0.65    ~spl7_7 | spl7_8),
% 1.10/0.65    inference(avatar_split_clause,[],[f30,f88,f84])).
% 1.10/0.65  fof(f30,plain,(
% 1.10/0.65    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  fof(f82,plain,(
% 1.10/0.65    spl7_1 | spl7_6),
% 1.10/0.65    inference(avatar_split_clause,[],[f31,f80,f56])).
% 1.10/0.65  fof(f31,plain,(
% 1.10/0.65    ( ! [X6,X5] : (X5 = X6 | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | ~r2_hidden(X6,sK0) | ~r2_hidden(X5,sK0) | v2_funct_1(sK2)) )),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  fof(f78,plain,(
% 1.10/0.65    ~spl7_1 | spl7_5),
% 1.10/0.65    inference(avatar_split_clause,[],[f32,f75,f56])).
% 1.10/0.65  fof(f32,plain,(
% 1.10/0.65    r2_hidden(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  fof(f73,plain,(
% 1.10/0.65    ~spl7_1 | spl7_4),
% 1.10/0.65    inference(avatar_split_clause,[],[f33,f70,f56])).
% 1.10/0.65  fof(f33,plain,(
% 1.10/0.65    r2_hidden(sK4,sK0) | ~v2_funct_1(sK2)),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  fof(f68,plain,(
% 1.10/0.65    ~spl7_1 | spl7_3),
% 1.10/0.65    inference(avatar_split_clause,[],[f34,f65,f56])).
% 1.10/0.65  fof(f34,plain,(
% 1.10/0.65    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~v2_funct_1(sK2)),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  fof(f63,plain,(
% 1.10/0.65    ~spl7_1 | ~spl7_2),
% 1.10/0.65    inference(avatar_split_clause,[],[f35,f60,f56])).
% 1.10/0.65  fof(f35,plain,(
% 1.10/0.65    sK3 != sK4 | ~v2_funct_1(sK2)),
% 1.10/0.65    inference(cnf_transformation,[],[f21])).
% 1.10/0.65  % SZS output end Proof for theBenchmark
% 1.10/0.65  % (24385)------------------------------
% 1.10/0.65  % (24385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.65  % (24385)Termination reason: Refutation
% 1.10/0.65  
% 1.10/0.65  % (24385)Memory used [KB]: 10746
% 1.10/0.65  % (24385)Time elapsed: 0.073 s
% 1.10/0.65  % (24385)------------------------------
% 1.10/0.65  % (24385)------------------------------
% 1.10/0.65  % (24241)Success in time 0.294 s
%------------------------------------------------------------------------------
