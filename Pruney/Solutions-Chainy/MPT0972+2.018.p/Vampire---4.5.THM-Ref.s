%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:07 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 721 expanded)
%              Number of leaves         :   15 ( 222 expanded)
%              Depth                    :   28
%              Number of atoms          :  632 (4861 expanded)
%              Number of equality atoms :  165 ( 960 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f774,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f228,f266,f329,f372,f762,f769])).

fof(f769,plain,
    ( ~ spl7_4
    | spl7_12
    | spl7_14
    | ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f768])).

fof(f768,plain,
    ( $false
    | ~ spl7_4
    | spl7_12
    | spl7_14
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f767,f766])).

fof(f766,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | ~ spl7_4
    | spl7_12
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f765,f84])).

fof(f84,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
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
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f765,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl7_4
    | spl7_12
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f764,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f764,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_4
    | spl7_12
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f752,f177])).

fof(f177,plain,
    ( sK2 != sK3
    | spl7_12 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl7_12
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f752,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(trivial_inequality_removal,[],[f751])).

fof(f751,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(superposition,[],[f592,f607])).

fof(f607,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(backward_demodulation,[],[f549,f606])).

fof(f606,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f544,f504])).

fof(f504,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f278,f328])).

fof(f328,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl7_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f278,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f42,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f544,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(resolution,[],[f503,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f503,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f279,f328])).

fof(f279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f43,f109])).

fof(f549,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(resolution,[],[f503,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f592,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | r2_hidden(sK4(X0,sK3),k1_xboole_0)
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(inner_rewriting,[],[f591])).

fof(f591,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f590,f122])).

fof(f122,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f46,f61])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f590,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f587,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f587,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(superposition,[],[f50,f577])).

fof(f577,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(backward_demodulation,[],[f530,f576])).

fof(f576,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f525,f491])).

fof(f491,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f280,f328])).

fof(f280,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f45,f109])).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f525,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(resolution,[],[f490,f78])).

fof(f490,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f281,f328])).

fof(f281,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f46,f109])).

fof(f530,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_17 ),
    inference(resolution,[],[f490,f62])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f767,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | spl7_14
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f240,f328])).

fof(f240,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK0)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl7_14
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f762,plain,
    ( ~ spl7_4
    | spl7_12
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | ~ spl7_4
    | spl7_12
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f760,f607])).

fof(f760,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl7_4
    | spl7_12
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f759,f577])).

fof(f759,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | spl7_12
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f758,f84])).

fof(f758,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl7_12
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f757,f41])).

fof(f757,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_12
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f756,f122])).

fof(f756,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_12
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f755,f44])).

fof(f755,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_12
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f754,f177])).

fof(f754,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(trivial_inequality_removal,[],[f753])).

fof(f753,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(superposition,[],[f51,f595])).

fof(f595,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(resolution,[],[f585,f517])).

fof(f517,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f47,f328])).

fof(f47,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f585,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_17 ),
    inference(forward_demodulation,[],[f241,f328])).

fof(f241,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f239])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f372,plain,
    ( ~ spl7_4
    | spl7_12
    | ~ spl7_16
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl7_4
    | spl7_12
    | ~ spl7_16
    | spl7_17 ),
    inference(subsumption_resolution,[],[f370,f340])).

fof(f340,plain,
    ( k1_xboole_0 != sK3
    | spl7_12
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f177,f324])).

fof(f324,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl7_16
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f370,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_4
    | spl7_17 ),
    inference(subsumption_resolution,[],[f369,f327])).

fof(f327,plain,
    ( k1_xboole_0 != sK0
    | spl7_17 ),
    inference(avatar_component_clause,[],[f326])).

fof(f369,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f359,f280])).

fof(f359,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(resolution,[],[f281,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f329,plain,
    ( spl7_16
    | spl7_17
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f320,f107,f326,f322])).

fof(f320,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f310,f278])).

fof(f310,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_4 ),
    inference(resolution,[],[f279,f76])).

fof(f266,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f252,f89])).

fof(f89,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f43,f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f252,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f48,f178])).

fof(f178,plain,
    ( sK2 = sK3
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f176])).

fof(f48,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f228,plain,
    ( ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f226,f120])).

fof(f120,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f85,f105])).

fof(f105,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f85,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f43,f62])).

fof(f226,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(forward_demodulation,[],[f225,f132])).

fof(f132,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl7_4 ),
    inference(backward_demodulation,[],[f123,f131])).

fof(f131,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f130,f108])).

fof(f108,plain,
    ( k1_xboole_0 != sK1
    | spl7_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f130,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f124,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f123,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f46,f62])).

fof(f225,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f224,f122])).

fof(f224,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f223,f44])).

fof(f223,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f222,f84])).

fof(f222,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f221,f41])).

fof(f221,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f220,f177])).

fof(f220,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(trivial_inequality_removal,[],[f219])).

fof(f219,plain,
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
    inference(superposition,[],[f51,f192])).

fof(f192,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(resolution,[],[f191,f47])).

fof(f191,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f190,f122])).

fof(f190,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f189,f44])).

fof(f189,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4
    | spl7_12 ),
    inference(subsumption_resolution,[],[f188,f177])).

fof(f188,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4 ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | spl7_4 ),
    inference(superposition,[],[f138,f132])).

fof(f138,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_3 ),
    inference(inner_rewriting,[],[f137])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f136,f84])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f134,f41])).

fof(f134,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f50,f120])).

fof(f110,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f101,f107,f103])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f86,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f43,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:31:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.53/0.57  % (5274)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.57  % (5266)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.53/0.58  % (5273)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.58  % (5275)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.58  % (5271)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.58  % (5283)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.58  % (5267)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.58  % (5268)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.53/0.59  % (5275)Refutation not found, incomplete strategy% (5275)------------------------------
% 1.53/0.59  % (5275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (5270)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.60  % (5269)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.53/0.60  % (5291)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.60  % (5265)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.53/0.60  % (5275)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (5275)Memory used [KB]: 10746
% 1.53/0.60  % (5275)Time elapsed: 0.149 s
% 1.53/0.60  % (5275)------------------------------
% 1.53/0.60  % (5275)------------------------------
% 1.53/0.60  % (5282)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.60  % (5289)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.61  % (5293)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.61  % (5284)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.61  % (5276)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.61  % (5280)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.61  % (5282)Refutation not found, incomplete strategy% (5282)------------------------------
% 1.53/0.61  % (5282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.61  % (5286)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.53/0.61  % (5282)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.61  
% 1.53/0.61  % (5282)Memory used [KB]: 10746
% 1.53/0.61  % (5282)Time elapsed: 0.170 s
% 1.53/0.61  % (5282)------------------------------
% 1.53/0.61  % (5282)------------------------------
% 1.53/0.61  % (5285)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.61  % (5288)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.62  % (5292)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.62  % (5294)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.62  % (5281)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.62  % (5287)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.53/0.63  % (5277)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.63  % (5272)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.63  % (5290)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.63  % (5276)Refutation not found, incomplete strategy% (5276)------------------------------
% 1.53/0.63  % (5276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.63  % (5276)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.63  
% 1.53/0.63  % (5276)Memory used [KB]: 10746
% 1.53/0.63  % (5276)Time elapsed: 0.204 s
% 1.53/0.63  % (5276)------------------------------
% 1.53/0.63  % (5276)------------------------------
% 1.53/0.63  % (5273)Refutation found. Thanks to Tanya!
% 1.53/0.63  % SZS status Theorem for theBenchmark
% 1.53/0.63  % SZS output start Proof for theBenchmark
% 1.53/0.63  fof(f774,plain,(
% 1.53/0.63    $false),
% 1.53/0.63    inference(avatar_sat_refutation,[],[f110,f228,f266,f329,f372,f762,f769])).
% 1.53/0.63  fof(f769,plain,(
% 1.53/0.63    ~spl7_4 | spl7_12 | spl7_14 | ~spl7_17),
% 1.53/0.63    inference(avatar_contradiction_clause,[],[f768])).
% 1.53/0.63  fof(f768,plain,(
% 1.53/0.63    $false | (~spl7_4 | spl7_12 | spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f767,f766])).
% 1.53/0.63  fof(f766,plain,(
% 1.53/0.63    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | (~spl7_4 | spl7_12 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f765,f84])).
% 1.53/0.63  fof(f84,plain,(
% 1.53/0.63    v1_relat_1(sK2)),
% 1.53/0.63    inference(resolution,[],[f43,f61])).
% 1.53/0.63  fof(f61,plain,(
% 1.53/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.53/0.63    inference(cnf_transformation,[],[f20])).
% 1.53/0.63  fof(f20,plain,(
% 1.53/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.63    inference(ennf_transformation,[],[f7])).
% 1.53/0.63  fof(f7,axiom,(
% 1.53/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.53/0.63  fof(f43,plain,(
% 1.53/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.63    inference(cnf_transformation,[],[f29])).
% 1.53/0.63  fof(f29,plain,(
% 1.53/0.63    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.53/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f28,f27])).
% 1.53/0.63  fof(f27,plain,(
% 1.53/0.63    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.53/0.63    introduced(choice_axiom,[])).
% 1.53/0.63  fof(f28,plain,(
% 1.53/0.63    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.53/0.63    introduced(choice_axiom,[])).
% 1.53/0.63  fof(f15,plain,(
% 1.53/0.63    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/0.63    inference(flattening,[],[f14])).
% 1.53/0.63  fof(f14,plain,(
% 1.53/0.63    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.53/0.63    inference(ennf_transformation,[],[f13])).
% 1.53/0.63  fof(f13,negated_conjecture,(
% 1.53/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.53/0.63    inference(negated_conjecture,[],[f12])).
% 1.53/0.63  fof(f12,conjecture,(
% 1.53/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 1.53/0.63  fof(f765,plain,(
% 1.53/0.63    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | ~v1_relat_1(sK2) | (~spl7_4 | spl7_12 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f764,f41])).
% 1.53/0.63  fof(f41,plain,(
% 1.53/0.63    v1_funct_1(sK2)),
% 1.53/0.63    inference(cnf_transformation,[],[f29])).
% 1.53/0.63  fof(f764,plain,(
% 1.53/0.63    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_4 | spl7_12 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f752,f177])).
% 1.53/0.63  fof(f177,plain,(
% 1.53/0.63    sK2 != sK3 | spl7_12),
% 1.53/0.63    inference(avatar_component_clause,[],[f176])).
% 1.53/0.63  fof(f176,plain,(
% 1.53/0.63    spl7_12 <=> sK2 = sK3),
% 1.53/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.53/0.63  fof(f752,plain,(
% 1.53/0.63    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(trivial_inequality_removal,[],[f751])).
% 1.53/0.63  fof(f751,plain,(
% 1.53/0.63    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK4(sK2,sK3),k1_xboole_0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(superposition,[],[f592,f607])).
% 1.53/0.63  fof(f607,plain,(
% 1.53/0.63    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(backward_demodulation,[],[f549,f606])).
% 1.53/0.63  fof(f606,plain,(
% 1.53/0.63    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f544,f504])).
% 1.53/0.63  fof(f504,plain,(
% 1.53/0.63    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(forward_demodulation,[],[f278,f328])).
% 1.53/0.63  fof(f328,plain,(
% 1.53/0.63    k1_xboole_0 = sK0 | ~spl7_17),
% 1.53/0.63    inference(avatar_component_clause,[],[f326])).
% 1.53/0.63  fof(f326,plain,(
% 1.53/0.63    spl7_17 <=> k1_xboole_0 = sK0),
% 1.53/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.53/0.63  fof(f278,plain,(
% 1.53/0.63    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_4),
% 1.53/0.63    inference(backward_demodulation,[],[f42,f109])).
% 1.53/0.63  fof(f109,plain,(
% 1.53/0.63    k1_xboole_0 = sK1 | ~spl7_4),
% 1.53/0.63    inference(avatar_component_clause,[],[f107])).
% 1.53/0.63  fof(f107,plain,(
% 1.53/0.63    spl7_4 <=> k1_xboole_0 = sK1),
% 1.53/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.53/0.63  fof(f42,plain,(
% 1.53/0.63    v1_funct_2(sK2,sK0,sK1)),
% 1.53/0.63    inference(cnf_transformation,[],[f29])).
% 1.53/0.63  fof(f544,plain,(
% 1.53/0.63    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(resolution,[],[f503,f78])).
% 1.53/0.63  fof(f78,plain,(
% 1.53/0.63    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.53/0.63    inference(equality_resolution,[],[f64])).
% 1.53/0.63  fof(f64,plain,(
% 1.53/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.63    inference(cnf_transformation,[],[f39])).
% 1.53/0.63  fof(f39,plain,(
% 1.53/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.63    inference(nnf_transformation,[],[f23])).
% 1.53/0.63  fof(f23,plain,(
% 1.53/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.63    inference(flattening,[],[f22])).
% 1.53/0.63  fof(f22,plain,(
% 1.53/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.63    inference(ennf_transformation,[],[f11])).
% 1.53/0.63  fof(f11,axiom,(
% 1.53/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.53/0.63  fof(f503,plain,(
% 1.53/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(forward_demodulation,[],[f279,f328])).
% 1.53/0.63  fof(f279,plain,(
% 1.53/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_4),
% 1.53/0.63    inference(backward_demodulation,[],[f43,f109])).
% 1.53/0.63  fof(f549,plain,(
% 1.53/0.63    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(resolution,[],[f503,f62])).
% 1.53/0.63  fof(f62,plain,(
% 1.53/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.53/0.63    inference(cnf_transformation,[],[f21])).
% 1.53/0.63  fof(f21,plain,(
% 1.53/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.63    inference(ennf_transformation,[],[f9])).
% 1.53/0.63  fof(f9,axiom,(
% 1.53/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.53/0.63  fof(f592,plain,(
% 1.53/0.63    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | r2_hidden(sK4(X0,sK3),k1_xboole_0) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(inner_rewriting,[],[f591])).
% 1.53/0.63  fof(f591,plain,(
% 1.53/0.63    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f590,f122])).
% 1.53/0.63  fof(f122,plain,(
% 1.53/0.63    v1_relat_1(sK3)),
% 1.53/0.63    inference(resolution,[],[f46,f61])).
% 1.53/0.63  fof(f46,plain,(
% 1.53/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.63    inference(cnf_transformation,[],[f29])).
% 1.53/0.63  fof(f590,plain,(
% 1.53/0.63    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0 | ~v1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f587,f44])).
% 1.53/0.63  fof(f44,plain,(
% 1.53/0.63    v1_funct_1(sK3)),
% 1.53/0.63    inference(cnf_transformation,[],[f29])).
% 1.53/0.63  fof(f587,plain,(
% 1.53/0.63    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | r2_hidden(sK4(X0,sK3),k1_relat_1(X0)) | sK3 = X0 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(superposition,[],[f50,f577])).
% 1.53/0.63  fof(f577,plain,(
% 1.53/0.63    k1_xboole_0 = k1_relat_1(sK3) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(backward_demodulation,[],[f530,f576])).
% 1.53/0.63  fof(f576,plain,(
% 1.53/0.63    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f525,f491])).
% 1.53/0.63  fof(f491,plain,(
% 1.53/0.63    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(forward_demodulation,[],[f280,f328])).
% 1.53/0.63  fof(f280,plain,(
% 1.53/0.63    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_4),
% 1.53/0.63    inference(backward_demodulation,[],[f45,f109])).
% 1.53/0.63  fof(f45,plain,(
% 1.53/0.63    v1_funct_2(sK3,sK0,sK1)),
% 1.53/0.63    inference(cnf_transformation,[],[f29])).
% 1.53/0.63  fof(f525,plain,(
% 1.53/0.63    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(resolution,[],[f490,f78])).
% 1.53/0.63  fof(f490,plain,(
% 1.53/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(forward_demodulation,[],[f281,f328])).
% 1.53/0.63  fof(f281,plain,(
% 1.53/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_4),
% 1.53/0.63    inference(backward_demodulation,[],[f46,f109])).
% 1.53/0.63  fof(f530,plain,(
% 1.53/0.63    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl7_4 | ~spl7_17)),
% 1.53/0.63    inference(resolution,[],[f490,f62])).
% 1.53/0.63  fof(f50,plain,(
% 1.53/0.63    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.63    inference(cnf_transformation,[],[f31])).
% 1.53/0.63  fof(f31,plain,(
% 1.53/0.63    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).
% 1.53/0.63  fof(f30,plain,(
% 1.53/0.63    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.53/0.63    introduced(choice_axiom,[])).
% 1.53/0.63  fof(f17,plain,(
% 1.53/0.63    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.63    inference(flattening,[],[f16])).
% 1.53/0.63  fof(f16,plain,(
% 1.53/0.63    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.63    inference(ennf_transformation,[],[f6])).
% 1.53/0.63  fof(f6,axiom,(
% 1.53/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.53/0.63  fof(f767,plain,(
% 1.53/0.63    ~r2_hidden(sK4(sK2,sK3),k1_xboole_0) | (spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(forward_demodulation,[],[f240,f328])).
% 1.53/0.63  fof(f240,plain,(
% 1.53/0.63    ~r2_hidden(sK4(sK2,sK3),sK0) | spl7_14),
% 1.53/0.63    inference(avatar_component_clause,[],[f239])).
% 1.53/0.63  fof(f239,plain,(
% 1.53/0.63    spl7_14 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 1.53/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.53/0.63  fof(f762,plain,(
% 1.53/0.63    ~spl7_4 | spl7_12 | ~spl7_14 | ~spl7_17),
% 1.53/0.63    inference(avatar_contradiction_clause,[],[f761])).
% 1.53/0.63  fof(f761,plain,(
% 1.53/0.63    $false | (~spl7_4 | spl7_12 | ~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f760,f607])).
% 1.53/0.63  fof(f760,plain,(
% 1.53/0.63    k1_xboole_0 != k1_relat_1(sK2) | (~spl7_4 | spl7_12 | ~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(forward_demodulation,[],[f759,f577])).
% 1.53/0.63  fof(f759,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | (spl7_12 | ~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f758,f84])).
% 1.53/0.63  fof(f758,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (spl7_12 | ~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f757,f41])).
% 1.53/0.63  fof(f757,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_12 | ~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f756,f122])).
% 1.53/0.63  fof(f756,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_12 | ~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f755,f44])).
% 1.53/0.63  fof(f755,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_12 | ~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f754,f177])).
% 1.53/0.63  fof(f754,plain,(
% 1.53/0.63    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(trivial_inequality_removal,[],[f753])).
% 1.53/0.63  fof(f753,plain,(
% 1.53/0.63    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(superposition,[],[f51,f595])).
% 1.53/0.63  fof(f595,plain,(
% 1.53/0.63    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(resolution,[],[f585,f517])).
% 1.53/0.63  fof(f517,plain,(
% 1.53/0.63    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) ) | ~spl7_17),
% 1.53/0.63    inference(forward_demodulation,[],[f47,f328])).
% 1.53/0.63  fof(f47,plain,(
% 1.53/0.63    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.53/0.63    inference(cnf_transformation,[],[f29])).
% 1.53/0.63  fof(f585,plain,(
% 1.53/0.63    r2_hidden(sK4(sK2,sK3),k1_xboole_0) | (~spl7_14 | ~spl7_17)),
% 1.53/0.63    inference(forward_demodulation,[],[f241,f328])).
% 1.53/0.63  fof(f241,plain,(
% 1.53/0.63    r2_hidden(sK4(sK2,sK3),sK0) | ~spl7_14),
% 1.53/0.63    inference(avatar_component_clause,[],[f239])).
% 1.53/0.63  fof(f51,plain,(
% 1.53/0.63    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.63    inference(cnf_transformation,[],[f31])).
% 1.53/0.63  fof(f372,plain,(
% 1.53/0.63    ~spl7_4 | spl7_12 | ~spl7_16 | spl7_17),
% 1.53/0.63    inference(avatar_contradiction_clause,[],[f371])).
% 1.53/0.63  fof(f371,plain,(
% 1.53/0.63    $false | (~spl7_4 | spl7_12 | ~spl7_16 | spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f370,f340])).
% 1.53/0.63  fof(f340,plain,(
% 1.53/0.63    k1_xboole_0 != sK3 | (spl7_12 | ~spl7_16)),
% 1.53/0.63    inference(backward_demodulation,[],[f177,f324])).
% 1.53/0.63  fof(f324,plain,(
% 1.53/0.63    k1_xboole_0 = sK2 | ~spl7_16),
% 1.53/0.63    inference(avatar_component_clause,[],[f322])).
% 1.53/0.63  fof(f322,plain,(
% 1.53/0.63    spl7_16 <=> k1_xboole_0 = sK2),
% 1.53/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.53/0.63  fof(f370,plain,(
% 1.53/0.63    k1_xboole_0 = sK3 | (~spl7_4 | spl7_17)),
% 1.53/0.63    inference(subsumption_resolution,[],[f369,f327])).
% 1.53/0.63  fof(f327,plain,(
% 1.53/0.63    k1_xboole_0 != sK0 | spl7_17),
% 1.53/0.63    inference(avatar_component_clause,[],[f326])).
% 1.53/0.63  fof(f369,plain,(
% 1.53/0.63    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl7_4),
% 1.53/0.63    inference(subsumption_resolution,[],[f359,f280])).
% 1.53/0.63  fof(f359,plain,(
% 1.53/0.63    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl7_4),
% 1.53/0.63    inference(resolution,[],[f281,f76])).
% 1.53/0.63  fof(f76,plain,(
% 1.53/0.63    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.53/0.63    inference(equality_resolution,[],[f67])).
% 1.53/0.63  fof(f67,plain,(
% 1.53/0.63    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.63    inference(cnf_transformation,[],[f39])).
% 1.53/0.63  fof(f329,plain,(
% 1.53/0.63    spl7_16 | spl7_17 | ~spl7_4),
% 1.53/0.63    inference(avatar_split_clause,[],[f320,f107,f326,f322])).
% 1.53/0.63  fof(f320,plain,(
% 1.53/0.63    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_4),
% 1.53/0.63    inference(subsumption_resolution,[],[f310,f278])).
% 1.53/0.63  fof(f310,plain,(
% 1.53/0.63    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_4),
% 1.53/0.63    inference(resolution,[],[f279,f76])).
% 1.53/0.63  fof(f266,plain,(
% 1.53/0.63    ~spl7_12),
% 1.53/0.63    inference(avatar_contradiction_clause,[],[f265])).
% 1.53/0.63  fof(f265,plain,(
% 1.53/0.63    $false | ~spl7_12),
% 1.53/0.63    inference(subsumption_resolution,[],[f252,f89])).
% 1.53/0.63  fof(f89,plain,(
% 1.53/0.63    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.53/0.63    inference(resolution,[],[f43,f82])).
% 1.53/0.63  fof(f82,plain,(
% 1.53/0.63    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.53/0.63    inference(duplicate_literal_removal,[],[f79])).
% 1.53/0.63  fof(f79,plain,(
% 1.53/0.63    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.63    inference(equality_resolution,[],[f71])).
% 1.53/0.63  fof(f71,plain,(
% 1.53/0.63    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.63    inference(cnf_transformation,[],[f40])).
% 1.53/0.63  fof(f40,plain,(
% 1.53/0.63    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.63    inference(nnf_transformation,[],[f26])).
% 1.53/0.63  fof(f26,plain,(
% 1.53/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.63    inference(flattening,[],[f25])).
% 1.53/0.63  fof(f25,plain,(
% 1.53/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.53/0.63    inference(ennf_transformation,[],[f10])).
% 1.53/0.63  fof(f10,axiom,(
% 1.53/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.53/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.53/0.63  fof(f252,plain,(
% 1.53/0.63    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_12),
% 1.53/0.63    inference(backward_demodulation,[],[f48,f178])).
% 1.53/0.63  fof(f178,plain,(
% 1.53/0.63    sK2 = sK3 | ~spl7_12),
% 1.53/0.63    inference(avatar_component_clause,[],[f176])).
% 1.53/0.63  fof(f48,plain,(
% 1.53/0.63    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.53/0.63    inference(cnf_transformation,[],[f29])).
% 1.53/0.63  fof(f228,plain,(
% 1.53/0.63    ~spl7_3 | spl7_4 | spl7_12),
% 1.53/0.63    inference(avatar_contradiction_clause,[],[f227])).
% 1.53/0.63  fof(f227,plain,(
% 1.53/0.63    $false | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f226,f120])).
% 1.53/0.63  fof(f120,plain,(
% 1.53/0.63    sK0 = k1_relat_1(sK2) | ~spl7_3),
% 1.53/0.63    inference(backward_demodulation,[],[f85,f105])).
% 1.53/0.63  fof(f105,plain,(
% 1.53/0.63    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_3),
% 1.53/0.63    inference(avatar_component_clause,[],[f103])).
% 1.53/0.63  fof(f103,plain,(
% 1.53/0.63    spl7_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.53/0.63  fof(f85,plain,(
% 1.53/0.63    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.53/0.63    inference(resolution,[],[f43,f62])).
% 1.53/0.63  fof(f226,plain,(
% 1.53/0.63    sK0 != k1_relat_1(sK2) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(forward_demodulation,[],[f225,f132])).
% 1.53/0.63  fof(f132,plain,(
% 1.53/0.63    sK0 = k1_relat_1(sK3) | spl7_4),
% 1.53/0.63    inference(backward_demodulation,[],[f123,f131])).
% 1.53/0.63  fof(f131,plain,(
% 1.53/0.63    sK0 = k1_relset_1(sK0,sK1,sK3) | spl7_4),
% 1.53/0.63    inference(subsumption_resolution,[],[f130,f108])).
% 1.53/0.63  fof(f108,plain,(
% 1.53/0.63    k1_xboole_0 != sK1 | spl7_4),
% 1.53/0.63    inference(avatar_component_clause,[],[f107])).
% 1.53/0.63  fof(f130,plain,(
% 1.53/0.63    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.53/0.63    inference(subsumption_resolution,[],[f124,f45])).
% 1.53/0.63  fof(f124,plain,(
% 1.53/0.63    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.53/0.63    inference(resolution,[],[f46,f63])).
% 1.53/0.63  fof(f63,plain,(
% 1.53/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.53/0.63    inference(cnf_transformation,[],[f39])).
% 1.53/0.63  fof(f123,plain,(
% 1.53/0.63    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.53/0.63    inference(resolution,[],[f46,f62])).
% 1.53/0.63  fof(f225,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f224,f122])).
% 1.53/0.63  fof(f224,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f223,f44])).
% 1.53/0.63  fof(f223,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f222,f84])).
% 1.53/0.63  fof(f222,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f221,f41])).
% 1.53/0.63  fof(f221,plain,(
% 1.53/0.63    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f220,f177])).
% 1.53/0.63  fof(f220,plain,(
% 1.53/0.63    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(trivial_inequality_removal,[],[f219])).
% 1.53/0.63  fof(f219,plain,(
% 1.53/0.63    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(superposition,[],[f51,f192])).
% 1.53/0.63  fof(f192,plain,(
% 1.53/0.63    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(resolution,[],[f191,f47])).
% 1.53/0.63  fof(f191,plain,(
% 1.53/0.63    r2_hidden(sK4(sK3,sK2),sK0) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f190,f122])).
% 1.53/0.63  fof(f190,plain,(
% 1.53/0.63    r2_hidden(sK4(sK3,sK2),sK0) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f189,f44])).
% 1.53/0.63  fof(f189,plain,(
% 1.53/0.63    r2_hidden(sK4(sK3,sK2),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4 | spl7_12)),
% 1.53/0.63    inference(subsumption_resolution,[],[f188,f177])).
% 1.53/0.63  fof(f188,plain,(
% 1.53/0.63    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4)),
% 1.53/0.63    inference(trivial_inequality_removal,[],[f187])).
% 1.53/0.63  fof(f187,plain,(
% 1.53/0.63    sK0 != sK0 | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | spl7_4)),
% 1.53/0.63    inference(superposition,[],[f138,f132])).
% 1.53/0.63  fof(f138,plain,(
% 1.53/0.63    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_3),
% 1.53/0.63    inference(inner_rewriting,[],[f137])).
% 1.53/0.63  fof(f137,plain,(
% 1.53/0.63    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_3),
% 1.53/0.63    inference(subsumption_resolution,[],[f136,f84])).
% 1.53/0.63  fof(f136,plain,(
% 1.53/0.63    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_3),
% 1.53/0.63    inference(subsumption_resolution,[],[f134,f41])).
% 1.53/0.63  fof(f134,plain,(
% 1.53/0.63    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_3),
% 1.53/0.63    inference(superposition,[],[f50,f120])).
% 1.53/0.63  fof(f110,plain,(
% 1.53/0.63    spl7_3 | spl7_4),
% 1.53/0.63    inference(avatar_split_clause,[],[f101,f107,f103])).
% 1.53/0.63  fof(f101,plain,(
% 1.53/0.63    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.63    inference(subsumption_resolution,[],[f86,f42])).
% 1.53/0.63  fof(f86,plain,(
% 1.53/0.63    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.63    inference(resolution,[],[f43,f63])).
% 1.53/0.63  % SZS output end Proof for theBenchmark
% 1.53/0.63  % (5273)------------------------------
% 1.53/0.63  % (5273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.63  % (5273)Termination reason: Refutation
% 1.53/0.63  
% 1.53/0.63  % (5273)Memory used [KB]: 10874
% 1.53/0.63  % (5273)Time elapsed: 0.207 s
% 1.53/0.63  % (5273)------------------------------
% 1.53/0.63  % (5273)------------------------------
% 1.53/0.64  % (5279)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.12/0.64  % (5264)Success in time 0.275 s
%------------------------------------------------------------------------------
