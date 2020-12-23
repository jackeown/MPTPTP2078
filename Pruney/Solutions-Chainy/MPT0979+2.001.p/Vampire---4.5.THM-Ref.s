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
% DateTime   : Thu Dec  3 13:01:25 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 995 expanded)
%              Number of leaves         :   12 ( 264 expanded)
%              Depth                    :   21
%              Number of atoms          :  568 (9255 expanded)
%              Number of equality atoms :  178 (3662 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f70,f140,f181,f251,f286])).

fof(f286,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f284,f114])).

fof(f114,plain,
    ( sK3 != sK4
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f34,f55])).

fof(f55,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl7_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f34,plain,
    ( sK3 != sK4
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f19,f18])).

fof(f18,plain,
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

fof(f19,plain,
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f8])).

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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f284,plain,
    ( sK3 = sK4
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f281,f186])).

fof(f186,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f60,f69])).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f60,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f281,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | sK3 = sK4
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(equality_resolution,[],[f271])).

fof(f271,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | sK4 = X0 )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f270,f209])).

fof(f209,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f208,f192])).

fof(f192,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f189,f191,f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f191,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f184,f69])).

fof(f184,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f28,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f189,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f185,f69])).

fof(f185,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f27,f64])).

fof(f27,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f208,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f207,f69])).

fof(f207,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f78,f64])).

fof(f78,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f28,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f270,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f269,f263])).

fof(f263,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f113,f69])).

fof(f113,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f32,f55])).

fof(f32,plain,
    ( r2_hidden(sK4,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k1_xboole_0)
        | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f268,f209])).

fof(f268,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f267,f74])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f28,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f267,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f266,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f266,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f264,f55])).

fof(f264,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f35,f115])).

fof(f115,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f33,f55])).

fof(f33,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f251,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f230,f79])).

fof(f79,plain,
    ( k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f74,f56,f26,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,
    ( ~ v2_funct_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f230,plain,
    ( k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK6(sK2))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f210,f77,f225,f188])).

fof(f188,plain,
    ( ! [X6,X5] :
        ( k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
        | ~ r2_hidden(X6,k1_xboole_0)
        | ~ r2_hidden(X5,k1_xboole_0)
        | X5 = X6 )
    | spl7_1
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f187,f69])).

fof(f187,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k1_xboole_0)
        | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
        | X5 = X6
        | ~ r2_hidden(X5,sK0) )
    | spl7_1
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f71,f69])).

% (25548)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f71,plain,
    ( ! [X6,X5] :
        ( k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
        | X5 = X6
        | ~ r2_hidden(X6,sK0)
        | ~ r2_hidden(X5,sK0) )
    | spl7_1 ),
    inference(subsumption_resolution,[],[f30,f56])).

fof(f30,plain,(
    ! [X6,X5] :
      ( X5 = X6
      | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6)
      | ~ r2_hidden(X6,sK0)
      | ~ r2_hidden(X5,sK0)
      | v2_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f225,plain,
    ( r2_hidden(sK6(sK2),k1_xboole_0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f224,f74])).

fof(f224,plain,
    ( r2_hidden(sK6(sK2),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f223,f26])).

fof(f223,plain,
    ( r2_hidden(sK6(sK2),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f211,f56])).

fof(f211,plain,
    ( r2_hidden(sK6(sK2),k1_xboole_0)
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f37,f209])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,
    ( sK5(sK2) != sK6(sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f74,f26,f56,f39])).

fof(f39,plain,(
    ! [X0] :
      ( sK5(X0) != sK6(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f210,plain,
    ( r2_hidden(sK5(sK2),k1_xboole_0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f75,f209])).

fof(f75,plain,
    ( r2_hidden(sK5(sK2),k1_relat_1(sK2))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f56,f26,f74,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f181,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f156,f77])).

fof(f156,plain,
    ( sK5(sK2) = sK6(sK2)
    | spl7_1
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f96,f95,f79,f71])).

fof(f95,plain,
    ( r2_hidden(sK6(sK2),sK0)
    | spl7_1
    | spl7_3 ),
    inference(backward_demodulation,[],[f76,f91])).

fof(f91,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl7_3 ),
    inference(backward_demodulation,[],[f78,f90])).

fof(f90,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f65,f27,f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,
    ( k1_xboole_0 != sK1
    | spl7_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f76,plain,
    ( r2_hidden(sK6(sK2),k1_relat_1(sK2))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f74,f26,f56,f37])).

fof(f96,plain,
    ( r2_hidden(sK5(sK2),sK0)
    | spl7_1
    | spl7_3 ),
    inference(backward_demodulation,[],[f75,f91])).

fof(f140,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(subsumption_resolution,[],[f138,f114])).

fof(f138,plain,
    ( sK3 = sK4
    | ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(subsumption_resolution,[],[f135,f60])).

fof(f135,plain,
    ( ~ r2_hidden(sK3,sK0)
    | sK3 = sK4
    | ~ spl7_1
    | spl7_3 ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,sK0)
        | sK4 = X0 )
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f124,f113])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,sK0)
        | ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0 )
    | ~ spl7_1
    | spl7_3 ),
    inference(forward_demodulation,[],[f123,f91])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(sK4,k1_relat_1(sK2)) )
    | ~ spl7_1
    | spl7_3 ),
    inference(forward_demodulation,[],[f122,f91])).

fof(f122,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(sK4,k1_relat_1(sK2)) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f121,f74])).

fof(f121,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f120,f26])).

fof(f120,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f116,f55])).

fof(f116,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0)
        | sK4 = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f35,f115])).

fof(f70,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f29,f67,f63])).

fof(f29,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f31,f58,f54])).

fof(f31,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:14:49 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.43  % (25531)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.18/0.45  % (25531)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.46  % (25539)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.18/0.47  % (25533)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.18/0.47  % (25535)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.18/0.47  % (25542)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.18/0.47  % (25550)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f287,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f61,f70,f140,f181,f251,f286])).
% 0.18/0.47  fof(f286,plain,(
% 0.18/0.47    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f285])).
% 0.18/0.47  fof(f285,plain,(
% 0.18/0.47    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.18/0.47    inference(subsumption_resolution,[],[f284,f114])).
% 0.18/0.47  fof(f114,plain,(
% 0.18/0.47    sK3 != sK4 | ~spl7_1),
% 0.18/0.47    inference(subsumption_resolution,[],[f34,f55])).
% 0.18/0.47  fof(f55,plain,(
% 0.18/0.47    v2_funct_1(sK2) | ~spl7_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f54])).
% 0.18/0.47  fof(f54,plain,(
% 0.18/0.47    spl7_1 <=> v2_funct_1(sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    sK3 != sK4 | ~v2_funct_1(sK2)),
% 0.18/0.47    inference(cnf_transformation,[],[f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ((sK3 != sK4 & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) & r2_hidden(sK4,sK0) & r2_hidden(sK3,sK0)) | ~v2_funct_1(sK2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | ~r2_hidden(X6,sK0) | ~r2_hidden(X5,sK0)) | v2_funct_1(sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f19,f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((? [X4,X3] : (X3 != X4 & k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4) & r2_hidden(X4,sK0) & r2_hidden(X3,sK0)) | ~v2_funct_1(sK2)) & (! [X6,X5] : (X5 = X6 | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | ~r2_hidden(X6,sK0) | ~r2_hidden(X5,sK0)) | v2_funct_1(sK2)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ? [X4,X3] : (X3 != X4 & k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4) & r2_hidden(X4,sK0) & r2_hidden(X3,sK0)) => (sK3 != sK4 & k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) & r2_hidden(sK4,sK0) & r2_hidden(sK3,sK0))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.18/0.47    inference(rectify,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ? [X0,X1,X2] : ((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | v2_funct_1(X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.18/0.47    inference(flattening,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (((? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) | ~v2_funct_1(X2)) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | v2_funct_1(X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.18/0.47    inference(nnf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,plain,(
% 0.18/0.47    ? [X0,X1,X2] : ((v2_funct_1(X2) <~> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.18/0.47    inference(flattening,[],[f7])).
% 0.18/0.47  fof(f7,plain,(
% 0.18/0.47    ? [X0,X1,X2] : (((v2_funct_1(X2) <~> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.18/0.47    inference(ennf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,negated_conjecture,(
% 0.18/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 0.18/0.47    inference(negated_conjecture,[],[f5])).
% 0.18/0.47  fof(f5,conjecture,(
% 0.18/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).
% 0.18/0.47  fof(f284,plain,(
% 0.18/0.47    sK3 = sK4 | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.18/0.47    inference(subsumption_resolution,[],[f281,f186])).
% 0.18/0.47  fof(f186,plain,(
% 0.18/0.47    r2_hidden(sK3,k1_xboole_0) | (~spl7_2 | ~spl7_4)),
% 0.18/0.47    inference(backward_demodulation,[],[f60,f69])).
% 0.18/0.47  fof(f69,plain,(
% 0.18/0.47    k1_xboole_0 = sK0 | ~spl7_4),
% 0.18/0.47    inference(avatar_component_clause,[],[f67])).
% 0.18/0.47  fof(f67,plain,(
% 0.18/0.47    spl7_4 <=> k1_xboole_0 = sK0),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.18/0.47  fof(f60,plain,(
% 0.18/0.47    r2_hidden(sK3,sK0) | ~spl7_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f58])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    spl7_2 <=> r2_hidden(sK3,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.18/0.47  fof(f281,plain,(
% 0.18/0.47    ~r2_hidden(sK3,k1_xboole_0) | sK3 = sK4 | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.47    inference(equality_resolution,[],[f271])).
% 0.18/0.47  fof(f271,plain,(
% 0.18/0.47    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | ~r2_hidden(X0,k1_xboole_0) | sK4 = X0) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.47    inference(forward_demodulation,[],[f270,f209])).
% 0.18/0.47  fof(f209,plain,(
% 0.18/0.47    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_3 | ~spl7_4)),
% 0.18/0.47    inference(forward_demodulation,[],[f208,f192])).
% 0.18/0.47  fof(f192,plain,(
% 0.18/0.47    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_3 | ~spl7_4)),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f189,f191,f52])).
% 0.18/0.47  fof(f52,plain,(
% 0.18/0.47    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.18/0.47    inference(equality_resolution,[],[f41])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f25])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(nnf_transformation,[],[f12])).
% 0.18/0.48  fof(f12,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(flattening,[],[f11])).
% 0.18/0.48  fof(f11,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f4])).
% 0.18/0.48  fof(f4,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.18/0.48  fof(f191,plain,(
% 0.18/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f184,f69])).
% 0.18/0.48  fof(f184,plain,(
% 0.18/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_3),
% 0.18/0.48    inference(backward_demodulation,[],[f28,f64])).
% 0.18/0.48  fof(f64,plain,(
% 0.18/0.48    k1_xboole_0 = sK1 | ~spl7_3),
% 0.18/0.48    inference(avatar_component_clause,[],[f63])).
% 0.18/0.48  fof(f63,plain,(
% 0.18/0.48    spl7_3 <=> k1_xboole_0 = sK1),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f189,plain,(
% 0.18/0.48    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f185,f69])).
% 0.18/0.48  fof(f185,plain,(
% 0.18/0.48    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_3),
% 0.18/0.48    inference(backward_demodulation,[],[f27,f64])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f208,plain,(
% 0.18/0.48    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f207,f69])).
% 0.18/0.48  fof(f207,plain,(
% 0.18/0.48    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) | ~spl7_3),
% 0.18/0.48    inference(forward_demodulation,[],[f78,f64])).
% 0.18/0.48  fof(f78,plain,(
% 0.18/0.48    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f28,f46])).
% 0.18/0.48  fof(f46,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f13])).
% 0.18/0.48  fof(f13,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.18/0.48  fof(f270,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(X0,k1_relat_1(sK2))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f269,f263])).
% 0.18/0.48  fof(f263,plain,(
% 0.18/0.48    r2_hidden(sK4,k1_xboole_0) | (~spl7_1 | ~spl7_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f113,f69])).
% 0.18/0.48  fof(f113,plain,(
% 0.18/0.48    r2_hidden(sK4,sK0) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f32,f55])).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    r2_hidden(sK4,sK0) | ~v2_funct_1(sK2)),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f269,plain,(
% 0.18/0.48    ( ! [X0] : (~r2_hidden(sK4,k1_xboole_0) | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(X0,k1_relat_1(sK2))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f268,f209])).
% 0.18/0.48  fof(f268,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f267,f74])).
% 0.18/0.48  fof(f74,plain,(
% 0.18/0.48    v1_relat_1(sK2)),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f28,f47])).
% 0.18/0.48  fof(f47,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f14])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.48  fof(f267,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f266,f26])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    v1_funct_1(sK2)),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f266,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f264,f55])).
% 0.18/0.48  fof(f264,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.18/0.48    inference(superposition,[],[f35,f115])).
% 0.18/0.48  fof(f115,plain,(
% 0.18/0.48    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f33,f55])).
% 0.18/0.48  fof(f33,plain,(
% 0.18/0.48    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~v2_funct_1(sK2)),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ! [X0] : (((v2_funct_1(X0) | (sK5(X0) != sK6(X0) & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f22,f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK5(X0) != sK6(X0) & k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0))))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(rectify,[],[f21])).
% 0.18/0.48  fof(f21,plain,(
% 0.18/0.48    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(nnf_transformation,[],[f10])).
% 0.18/0.48  fof(f10,plain,(
% 0.18/0.48    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(flattening,[],[f9])).
% 0.18/0.48  fof(f9,plain,(
% 0.18/0.48    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.18/0.48  fof(f251,plain,(
% 0.18/0.48    spl7_1 | ~spl7_3 | ~spl7_4),
% 0.18/0.48    inference(avatar_contradiction_clause,[],[f250])).
% 0.18/0.48  fof(f250,plain,(
% 0.18/0.48    $false | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f230,f79])).
% 0.18/0.48  fof(f79,plain,(
% 0.18/0.48    k1_funct_1(sK2,sK5(sK2)) = k1_funct_1(sK2,sK6(sK2)) | spl7_1),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f74,f56,f26,f38])).
% 0.18/0.48  fof(f38,plain,(
% 0.18/0.48    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0)) = k1_funct_1(X0,sK6(X0)) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f56,plain,(
% 0.18/0.48    ~v2_funct_1(sK2) | spl7_1),
% 0.18/0.48    inference(avatar_component_clause,[],[f54])).
% 0.18/0.48  fof(f230,plain,(
% 0.18/0.48    k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK6(sK2)) | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f210,f77,f225,f188])).
% 0.18/0.48  fof(f188,plain,(
% 0.18/0.48    ( ! [X6,X5] : (k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | ~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X5,k1_xboole_0) | X5 = X6) ) | (spl7_1 | ~spl7_4)),
% 0.18/0.48    inference(forward_demodulation,[],[f187,f69])).
% 0.18/0.48  fof(f187,plain,(
% 0.18/0.48    ( ! [X6,X5] : (~r2_hidden(X6,k1_xboole_0) | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | X5 = X6 | ~r2_hidden(X5,sK0)) ) | (spl7_1 | ~spl7_4)),
% 0.18/0.48    inference(backward_demodulation,[],[f71,f69])).
% 0.18/0.48  % (25548)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.18/0.48  fof(f71,plain,(
% 0.18/0.48    ( ! [X6,X5] : (k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | X5 = X6 | ~r2_hidden(X6,sK0) | ~r2_hidden(X5,sK0)) ) | spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f30,f56])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    ( ! [X6,X5] : (X5 = X6 | k1_funct_1(sK2,X5) != k1_funct_1(sK2,X6) | ~r2_hidden(X6,sK0) | ~r2_hidden(X5,sK0) | v2_funct_1(sK2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f225,plain,(
% 0.18/0.48    r2_hidden(sK6(sK2),k1_xboole_0) | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f224,f74])).
% 0.18/0.48  fof(f224,plain,(
% 0.18/0.48    r2_hidden(sK6(sK2),k1_xboole_0) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f223,f26])).
% 0.18/0.48  fof(f223,plain,(
% 0.18/0.48    r2_hidden(sK6(sK2),k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(subsumption_resolution,[],[f211,f56])).
% 0.18/0.48  fof(f211,plain,(
% 0.18/0.48    r2_hidden(sK6(sK2),k1_xboole_0) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(superposition,[],[f37,f209])).
% 0.18/0.48  fof(f37,plain,(
% 0.18/0.48    ( ! [X0] : (r2_hidden(sK6(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f77,plain,(
% 0.18/0.48    sK5(sK2) != sK6(sK2) | spl7_1),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f74,f26,f56,f39])).
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    ( ! [X0] : (sK5(X0) != sK6(X0) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f210,plain,(
% 0.18/0.48    r2_hidden(sK5(sK2),k1_xboole_0) | (spl7_1 | ~spl7_3 | ~spl7_4)),
% 0.18/0.48    inference(backward_demodulation,[],[f75,f209])).
% 0.18/0.48  fof(f75,plain,(
% 0.18/0.48    r2_hidden(sK5(sK2),k1_relat_1(sK2)) | spl7_1),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f56,f26,f74,f36])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f181,plain,(
% 0.18/0.48    spl7_1 | spl7_3),
% 0.18/0.48    inference(avatar_contradiction_clause,[],[f180])).
% 0.18/0.48  fof(f180,plain,(
% 0.18/0.48    $false | (spl7_1 | spl7_3)),
% 0.18/0.48    inference(subsumption_resolution,[],[f156,f77])).
% 0.18/0.48  fof(f156,plain,(
% 0.18/0.48    sK5(sK2) = sK6(sK2) | (spl7_1 | spl7_3)),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f96,f95,f79,f71])).
% 0.18/0.48  fof(f95,plain,(
% 0.18/0.48    r2_hidden(sK6(sK2),sK0) | (spl7_1 | spl7_3)),
% 0.18/0.48    inference(backward_demodulation,[],[f76,f91])).
% 0.18/0.48  fof(f91,plain,(
% 0.18/0.48    sK0 = k1_relat_1(sK2) | spl7_3),
% 0.18/0.48    inference(backward_demodulation,[],[f78,f90])).
% 0.18/0.48  fof(f90,plain,(
% 0.18/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | spl7_3),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f65,f27,f28,f40])).
% 0.18/0.48  fof(f40,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.18/0.48    inference(cnf_transformation,[],[f25])).
% 0.18/0.48  fof(f65,plain,(
% 0.18/0.48    k1_xboole_0 != sK1 | spl7_3),
% 0.18/0.48    inference(avatar_component_clause,[],[f63])).
% 0.18/0.48  fof(f76,plain,(
% 0.18/0.48    r2_hidden(sK6(sK2),k1_relat_1(sK2)) | spl7_1),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f74,f26,f56,f37])).
% 0.18/0.48  fof(f96,plain,(
% 0.18/0.48    r2_hidden(sK5(sK2),sK0) | (spl7_1 | spl7_3)),
% 0.18/0.48    inference(backward_demodulation,[],[f75,f91])).
% 0.18/0.48  fof(f140,plain,(
% 0.18/0.48    ~spl7_1 | ~spl7_2 | spl7_3),
% 0.18/0.48    inference(avatar_contradiction_clause,[],[f139])).
% 0.18/0.48  fof(f139,plain,(
% 0.18/0.48    $false | (~spl7_1 | ~spl7_2 | spl7_3)),
% 0.18/0.48    inference(subsumption_resolution,[],[f138,f114])).
% 0.18/0.48  fof(f138,plain,(
% 0.18/0.48    sK3 = sK4 | (~spl7_1 | ~spl7_2 | spl7_3)),
% 0.18/0.48    inference(subsumption_resolution,[],[f135,f60])).
% 0.18/0.48  fof(f135,plain,(
% 0.18/0.48    ~r2_hidden(sK3,sK0) | sK3 = sK4 | (~spl7_1 | spl7_3)),
% 0.18/0.48    inference(equality_resolution,[],[f125])).
% 0.18/0.48  fof(f125,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | ~r2_hidden(X0,sK0) | sK4 = X0) ) | (~spl7_1 | spl7_3)),
% 0.18/0.48    inference(subsumption_resolution,[],[f124,f113])).
% 0.18/0.48  fof(f124,plain,(
% 0.18/0.48    ( ! [X0] : (~r2_hidden(sK4,sK0) | ~r2_hidden(X0,sK0) | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0) ) | (~spl7_1 | spl7_3)),
% 0.18/0.48    inference(forward_demodulation,[],[f123,f91])).
% 0.18/0.48  fof(f123,plain,(
% 0.18/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(sK4,k1_relat_1(sK2))) ) | (~spl7_1 | spl7_3)),
% 0.18/0.48    inference(forward_demodulation,[],[f122,f91])).
% 0.18/0.48  fof(f122,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(sK4,k1_relat_1(sK2))) ) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f121,f74])).
% 0.18/0.48  fof(f121,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f120,f26])).
% 0.18/0.48  fof(f120,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f116,f55])).
% 0.18/0.48  fof(f116,plain,(
% 0.18/0.48    ( ! [X0] : (k1_funct_1(sK2,sK3) != k1_funct_1(sK2,X0) | sK4 = X0 | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.18/0.48    inference(superposition,[],[f35,f115])).
% 0.18/0.48  fof(f70,plain,(
% 0.18/0.48    ~spl7_3 | spl7_4),
% 0.18/0.48    inference(avatar_split_clause,[],[f29,f67,f63])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f61,plain,(
% 0.18/0.48    ~spl7_1 | spl7_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f31,f58,f54])).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    r2_hidden(sK3,sK0) | ~v2_funct_1(sK2)),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (25531)------------------------------
% 0.18/0.48  % (25531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (25531)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (25531)Memory used [KB]: 10746
% 0.18/0.48  % (25531)Time elapsed: 0.089 s
% 0.18/0.48  % (25531)------------------------------
% 0.18/0.48  % (25531)------------------------------
% 0.18/0.48  % (25530)Success in time 0.141 s
%------------------------------------------------------------------------------
