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
% DateTime   : Thu Dec  3 13:06:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 758 expanded)
%              Number of leaves         :   17 ( 234 expanded)
%              Depth                    :   28
%              Number of atoms          :  712 (4963 expanded)
%              Number of equality atoms :  182 ( 993 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f898,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f267,f311,f391,f444,f689,f696,f738,f897])).

fof(f897,plain,
    ( ~ spl7_4
    | spl7_12
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f896])).

fof(f896,plain,
    ( $false
    | ~ spl7_4
    | spl7_12
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f895,f729])).

fof(f729,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f651,f728])).

fof(f728,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f646,f611])).

fof(f611,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f325,f390])).

fof(f390,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl7_22
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f325,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f44,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f646,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(resolution,[],[f610,f81])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f610,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f326,f390])).

fof(f326,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f45,f112])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f651,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(resolution,[],[f610,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f895,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl7_4
    | spl7_12
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f894,f691])).

fof(f691,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f631,f690])).

fof(f690,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f626,f590])).

fof(f590,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f327,f390])).

fof(f327,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f47,f112])).

fof(f47,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f626,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(resolution,[],[f589,f81])).

fof(f589,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f328,f390])).

fof(f328,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f48,f112])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

% (11707)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f631,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(resolution,[],[f589,f65])).

fof(f894,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | spl7_12
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f893,f87])).

fof(f87,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f893,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl7_12
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f892,f43])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f892,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_12
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f891,f125])).

fof(f125,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f48,f64])).

fof(f891,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_12
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f890,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f890,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_12
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f889,f182])).

fof(f182,plain,
    ( sK2 != sK3
    | spl7_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_12
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f889,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(trivial_inequality_removal,[],[f888])).

fof(f888,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(superposition,[],[f53,f709])).

fof(f709,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(resolution,[],[f699,f623])).

fof(f623,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) )
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f136,f390])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ) ),
    inference(resolution,[],[f49,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f49,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f699,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f280,f390])).

fof(f280,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl7_19
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f738,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f737])).

fof(f737,plain,
    ( $false
    | spl7_3
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f736,f728])).

fof(f736,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f735,f390])).

fof(f735,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f107,f112])).

fof(f107,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl7_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f696,plain,
    ( ~ spl7_4
    | spl7_20
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | ~ spl7_4
    | spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f694,f690])).

fof(f694,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | spl7_20
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f693,f390])).

fof(f693,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl7_4
    | spl7_20 ),
    inference(forward_demodulation,[],[f322,f112])).

fof(f322,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl7_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f689,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_12
    | spl7_19
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | spl7_12
    | spl7_19
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f687,f125])).

fof(f687,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_12
    | spl7_19
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f686,f46])).

fof(f686,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_12
    | spl7_19
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f685,f182])).

fof(f685,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_19
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f684,f612])).

fof(f612,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | spl7_19
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f279,f390])).

fof(f279,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK0)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f278])).

fof(f684,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(trivial_inequality_removal,[],[f682])).

fof(f682,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(superposition,[],[f620,f587])).

fof(f587,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl7_4
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f586,f571])).

fof(f571,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f522,f390])).

fof(f522,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f323,f112])).

fof(f323,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f321])).

fof(f586,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f336,f390])).

fof(f336,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f126,f112])).

fof(f126,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f48,f65])).

fof(f620,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK2,X1),k1_xboole_0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl7_3
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f619,f390])).

fof(f619,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl7_3
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f143,f390])).

fof(f143,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f142,f87])).

fof(f142,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f138,f43])).

fof(f138,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3 ),
    inference(superposition,[],[f52,f123])).

fof(f123,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f88,f108])).

fof(f108,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f88,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f45,f65])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f444,plain,
    ( ~ spl7_4
    | spl7_12
    | ~ spl7_21
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f443])).

% (11720)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f443,plain,
    ( $false
    | ~ spl7_4
    | spl7_12
    | ~ spl7_21
    | spl7_22 ),
    inference(subsumption_resolution,[],[f442,f403])).

fof(f403,plain,
    ( k1_xboole_0 != sK3
    | spl7_12
    | ~ spl7_21 ),
    inference(backward_demodulation,[],[f182,f386])).

fof(f386,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl7_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f442,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_4
    | spl7_22 ),
    inference(subsumption_resolution,[],[f441,f389])).

fof(f389,plain,
    ( k1_xboole_0 != sK0
    | spl7_22 ),
    inference(avatar_component_clause,[],[f388])).

fof(f441,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f431,f327])).

fof(f431,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(resolution,[],[f328,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f391,plain,
    ( spl7_21
    | spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f382,f110,f388,f384])).

fof(f382,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f372,f325])).

fof(f372,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_4 ),
    inference(resolution,[],[f326,f79])).

fof(f311,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f291,f92])).

fof(f92,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f45,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f291,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f50,f183])).

fof(f183,plain,
    ( sK2 = sK3
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f50,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f267,plain,
    ( ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f265,f123])).

fof(f265,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(forward_demodulation,[],[f264,f135])).

fof(f135,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl7_4 ),
    inference(backward_demodulation,[],[f126,f134])).

fof(f134,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f133,f111])).

fof(f111,plain,
    ( k1_xboole_0 != sK1
    | spl7_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f133,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f127,f47])).

fof(f127,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f48,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f264,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f263,f125])).

fof(f263,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f262,f46])).

fof(f262,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f261,f87])).

fof(f261,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f260,f43])).

fof(f260,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f259,f182])).

fof(f259,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(superposition,[],[f53,f200])).

fof(f200,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(resolution,[],[f199,f136])).

% (11721)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f199,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f198,f125])).

fof(f198,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f197,f46])).

fof(f197,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f196,f182])).

fof(f196,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4 ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4 ),
    inference(superposition,[],[f141,f135])).

fof(f141,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_3 ),
    inference(inner_rewriting,[],[f140])).

fof(f140,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f139,f87])).

% (11698)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f139,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f52,f123])).

fof(f113,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f104,f110,f106])).

fof(f104,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f89,f44])).

fof(f89,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f45,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (11701)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (11693)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (11717)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (11696)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (11697)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (11706)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (11709)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (11715)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (11701)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f898,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f113,f267,f311,f391,f444,f689,f696,f738,f897])).
% 0.20/0.52  fof(f897,plain,(
% 0.20/0.52    ~spl7_4 | spl7_12 | ~spl7_19 | ~spl7_22),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f896])).
% 0.20/0.52  fof(f896,plain,(
% 0.20/0.52    $false | (~spl7_4 | spl7_12 | ~spl7_19 | ~spl7_22)),
% 0.20/0.52    inference(subsumption_resolution,[],[f895,f729])).
% 0.20/0.52  fof(f729,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_4 | ~spl7_22)),
% 0.20/0.52    inference(backward_demodulation,[],[f651,f728])).
% 0.20/0.52  fof(f728,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_4 | ~spl7_22)),
% 0.20/0.52    inference(subsumption_resolution,[],[f646,f611])).
% 0.20/0.52  fof(f611,plain,(
% 0.20/0.52    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_4 | ~spl7_22)),
% 0.20/0.52    inference(forward_demodulation,[],[f325,f390])).
% 0.20/0.52  fof(f390,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl7_22),
% 0.20/0.52    inference(avatar_component_clause,[],[f388])).
% 0.20/0.52  fof(f388,plain,(
% 0.20/0.52    spl7_22 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.52  fof(f325,plain,(
% 0.20/0.52    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_4),
% 0.20/0.52    inference(backward_demodulation,[],[f44,f112])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | ~spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f110])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    spl7_4 <=> k1_xboole_0 = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 0.20/0.52  fof(f646,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_4 | ~spl7_22)),
% 0.20/0.52    inference(resolution,[],[f610,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.20/0.52    inference(equality_resolution,[],[f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f610,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f326,f390])).
% 0.20/0.53  fof(f326,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_4),
% 0.20/0.53    inference(backward_demodulation,[],[f45,f112])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f651,plain,(
% 0.20/0.53    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(resolution,[],[f610,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f895,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relat_1(sK2) | (~spl7_4 | spl7_12 | ~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f894,f691])).
% 0.20/0.53  fof(f691,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(sK3) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(backward_demodulation,[],[f631,f690])).
% 0.20/0.53  fof(f690,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f626,f590])).
% 0.20/0.53  fof(f590,plain,(
% 0.20/0.53    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f327,f390])).
% 0.20/0.53  fof(f327,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_4),
% 0.20/0.53    inference(backward_demodulation,[],[f47,f112])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f626,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(resolution,[],[f589,f81])).
% 0.20/0.53  fof(f589,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f328,f390])).
% 0.20/0.53  fof(f328,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_4),
% 0.20/0.53    inference(backward_demodulation,[],[f48,f112])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  % (11707)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  fof(f631,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(resolution,[],[f589,f65])).
% 0.20/0.53  fof(f894,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | (spl7_12 | ~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f893,f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    v1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f45,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f893,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (spl7_12 | ~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f892,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f892,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_12 | ~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f891,f125])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    v1_relat_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f48,f64])).
% 0.20/0.53  fof(f891,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_12 | ~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f890,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f890,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_12 | ~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f889,f182])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    sK2 != sK3 | spl7_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f181])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    spl7_12 <=> sK2 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.53  fof(f889,plain,(
% 0.20/0.53    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f888])).
% 0.20/0.53  fof(f888,plain,(
% 0.20/0.53    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(superposition,[],[f53,f709])).
% 0.20/0.53  fof(f709,plain,(
% 0.20/0.53    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(resolution,[],[f699,f623])).
% 0.20/0.53  fof(f623,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)) ) | ~spl7_22),
% 0.20/0.53    inference(forward_demodulation,[],[f136,f390])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)) )),
% 0.20/0.53    inference(resolution,[],[f49,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X4] : (~m1_subset_1(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f699,plain,(
% 0.20/0.53    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | (~spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f280,f390])).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    r2_hidden(sK4(sK2,sK3),sK0) | ~spl7_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f278])).
% 0.20/0.53  fof(f278,plain,(
% 0.20/0.53    spl7_19 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.20/0.53  fof(f738,plain,(
% 0.20/0.53    spl7_3 | ~spl7_4 | ~spl7_22),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f737])).
% 0.20/0.53  fof(f737,plain,(
% 0.20/0.53    $false | (spl7_3 | ~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f736,f728])).
% 0.20/0.53  fof(f736,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl7_3 | ~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f735,f390])).
% 0.20/0.53  fof(f735,plain,(
% 0.20/0.53    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl7_3 | ~spl7_4)),
% 0.20/0.53    inference(forward_demodulation,[],[f107,f112])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    sK0 != k1_relset_1(sK0,sK1,sK2) | spl7_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl7_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.53  fof(f696,plain,(
% 0.20/0.53    ~spl7_4 | spl7_20 | ~spl7_22),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f695])).
% 0.20/0.53  fof(f695,plain,(
% 0.20/0.53    $false | (~spl7_4 | spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f694,f690])).
% 0.20/0.53  fof(f694,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f693,f390])).
% 0.20/0.53  fof(f693,plain,(
% 0.20/0.53    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl7_4 | spl7_20)),
% 0.20/0.53    inference(forward_demodulation,[],[f322,f112])).
% 0.20/0.53  fof(f322,plain,(
% 0.20/0.53    sK0 != k1_relset_1(sK0,sK1,sK3) | spl7_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f321])).
% 0.20/0.53  fof(f321,plain,(
% 0.20/0.53    spl7_20 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.53  fof(f689,plain,(
% 0.20/0.53    ~spl7_3 | ~spl7_4 | spl7_12 | spl7_19 | ~spl7_20 | ~spl7_22),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f688])).
% 0.20/0.53  fof(f688,plain,(
% 0.20/0.53    $false | (~spl7_3 | ~spl7_4 | spl7_12 | spl7_19 | ~spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f687,f125])).
% 0.20/0.53  fof(f687,plain,(
% 0.20/0.53    ~v1_relat_1(sK3) | (~spl7_3 | ~spl7_4 | spl7_12 | spl7_19 | ~spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f686,f46])).
% 0.20/0.53  fof(f686,plain,(
% 0.20/0.53    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | ~spl7_4 | spl7_12 | spl7_19 | ~spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f685,f182])).
% 0.20/0.53  fof(f685,plain,(
% 0.20/0.53    sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | ~spl7_4 | spl7_19 | ~spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f684,f612])).
% 0.20/0.53  fof(f612,plain,(
% 0.20/0.53    ~r2_hidden(sK4(sK2,sK3),k1_xboole_0) | (spl7_19 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f279,f390])).
% 0.20/0.53  fof(f279,plain,(
% 0.20/0.53    ~r2_hidden(sK4(sK2,sK3),sK0) | spl7_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f278])).
% 0.20/0.53  fof(f684,plain,(
% 0.20/0.53    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | ~spl7_4 | ~spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f682])).
% 0.20/0.53  fof(f682,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4(sK2,sK3),k1_xboole_0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | ~spl7_4 | ~spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(superposition,[],[f620,f587])).
% 0.20/0.53  fof(f587,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(sK3) | (~spl7_4 | ~spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f586,f571])).
% 0.20/0.53  fof(f571,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_20 | ~spl7_22)),
% 0.20/0.53    inference(backward_demodulation,[],[f522,f390])).
% 0.20/0.53  fof(f522,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_20)),
% 0.20/0.53    inference(forward_demodulation,[],[f323,f112])).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f321])).
% 0.20/0.53  fof(f586,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f336,f390])).
% 0.20/0.53  fof(f336,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl7_4),
% 0.20/0.53    inference(backward_demodulation,[],[f126,f112])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.53    inference(resolution,[],[f48,f65])).
% 0.20/0.53  fof(f620,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 != k1_relat_1(X1) | r2_hidden(sK4(sK2,X1),k1_xboole_0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl7_3 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f619,f390])).
% 0.20/0.53  fof(f619,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 != k1_relat_1(X1) | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl7_3 | ~spl7_22)),
% 0.20/0.53    inference(forward_demodulation,[],[f143,f390])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl7_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f142,f87])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | ~spl7_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f138,f43])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_3),
% 0.20/0.53    inference(superposition,[],[f52,f123])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | ~spl7_3),
% 0.20/0.53    inference(backward_demodulation,[],[f88,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f106])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f45,f65])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f444,plain,(
% 0.20/0.53    ~spl7_4 | spl7_12 | ~spl7_21 | spl7_22),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f443])).
% 0.20/0.53  % (11720)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  fof(f443,plain,(
% 0.20/0.53    $false | (~spl7_4 | spl7_12 | ~spl7_21 | spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f442,f403])).
% 0.20/0.53  fof(f403,plain,(
% 0.20/0.53    k1_xboole_0 != sK3 | (spl7_12 | ~spl7_21)),
% 0.20/0.53    inference(backward_demodulation,[],[f182,f386])).
% 0.20/0.53  fof(f386,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | ~spl7_21),
% 0.20/0.53    inference(avatar_component_clause,[],[f384])).
% 0.20/0.53  fof(f384,plain,(
% 0.20/0.53    spl7_21 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.53  fof(f442,plain,(
% 0.20/0.53    k1_xboole_0 = sK3 | (~spl7_4 | spl7_22)),
% 0.20/0.53    inference(subsumption_resolution,[],[f441,f389])).
% 0.20/0.53  fof(f389,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | spl7_22),
% 0.20/0.53    inference(avatar_component_clause,[],[f388])).
% 0.20/0.53  fof(f441,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl7_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f431,f327])).
% 0.20/0.53  fof(f431,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl7_4),
% 0.20/0.53    inference(resolution,[],[f328,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.20/0.53    inference(equality_resolution,[],[f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f391,plain,(
% 0.20/0.53    spl7_21 | spl7_22 | ~spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f382,f110,f388,f384])).
% 0.20/0.53  fof(f382,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f372,f325])).
% 0.20/0.53  fof(f372,plain,(
% 0.20/0.53    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_4),
% 0.20/0.53    inference(resolution,[],[f326,f79])).
% 0.20/0.53  fof(f311,plain,(
% 0.20/0.53    ~spl7_12),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f310])).
% 0.20/0.53  fof(f310,plain,(
% 0.20/0.53    $false | ~spl7_12),
% 0.20/0.53    inference(subsumption_resolution,[],[f291,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.53    inference(resolution,[],[f45,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_12),
% 0.20/0.53    inference(backward_demodulation,[],[f50,f183])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    sK2 = sK3 | ~spl7_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f181])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    ~spl7_3 | spl7_4 | spl7_12),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.53  fof(f266,plain,(
% 0.20/0.53    $false | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f265,f123])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    sK0 != k1_relat_1(sK2) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(forward_demodulation,[],[f264,f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | spl7_4),
% 0.20/0.53    inference(backward_demodulation,[],[f126,f134])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | spl7_4),
% 0.20/0.53    inference(subsumption_resolution,[],[f133,f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | spl7_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f110])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f127,f47])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.53    inference(resolution,[],[f48,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f263,f125])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f262,f46])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f261,f87])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f260,f43])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f259,f182])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f258])).
% 0.20/0.53  fof(f258,plain,(
% 0.20/0.53    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(superposition,[],[f53,f200])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(resolution,[],[f199,f136])).
% 0.20/0.53  % (11721)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    r2_hidden(sK4(sK3,sK2),sK0) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f198,f125])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    r2_hidden(sK4(sK3,sK2),sK0) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f197,f46])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    r2_hidden(sK4(sK3,sK2),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f196,f182])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f195])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    sK0 != sK0 | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4)),
% 0.20/0.53    inference(superposition,[],[f141,f135])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_3),
% 0.20/0.53    inference(inner_rewriting,[],[f140])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f139,f87])).
% 0.20/0.53  % (11698)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f137,f43])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_3),
% 0.20/0.53    inference(superposition,[],[f52,f123])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    spl7_3 | spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f104,f110,f106])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f89,f44])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.53    inference(resolution,[],[f45,f66])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (11701)------------------------------
% 0.20/0.53  % (11701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11701)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (11701)Memory used [KB]: 11001
% 0.20/0.53  % (11701)Time elapsed: 0.099 s
% 0.20/0.53  % (11701)------------------------------
% 0.20/0.53  % (11701)------------------------------
% 0.20/0.53  % (11711)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (11710)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (11692)Success in time 0.181 s
%------------------------------------------------------------------------------
