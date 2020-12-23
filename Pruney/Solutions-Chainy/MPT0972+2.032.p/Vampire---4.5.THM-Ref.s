%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:09 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 426 expanded)
%              Number of leaves         :   31 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  563 (2308 expanded)
%              Number of equality atoms :  136 ( 413 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f815,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f173,f179,f336,f339,f396,f399,f478,f614,f643,f663,f694,f701,f774,f789,f814])).

fof(f814,plain,(
    ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f813])).

fof(f813,plain,
    ( $false
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f92,f793])).

fof(f793,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_35 ),
    inference(backward_demodulation,[],[f55,f728])).

fof(f728,plain,
    ( sK2 = sK3
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl7_35
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f55,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f92,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f50,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f789,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | ~ spl7_12
    | ~ spl7_13
    | spl7_35
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f788,f772,f117,f101,f727,f329,f326,f389,f386])).

fof(f386,plain,
    ( spl7_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f389,plain,
    ( spl7_16
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f326,plain,
    ( spl7_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f329,plain,
    ( spl7_13
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f101,plain,
    ( spl7_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f117,plain,
    ( spl7_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f772,plain,
    ( spl7_40
  <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f788,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_40 ),
    inference(trivial_inequality_removal,[],[f787])).

fof(f787,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_40 ),
    inference(forward_demodulation,[],[f786,f699])).

fof(f699,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f95,f102])).

fof(f102,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f95,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f50,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f786,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | ~ spl7_40 ),
    inference(forward_demodulation,[],[f785,f703])).

fof(f703,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f111,f118])).

fof(f118,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f111,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f53,f72])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f785,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_40 ),
    inference(trivial_inequality_removal,[],[f784])).

fof(f784,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_40 ),
    inference(superposition,[],[f59,f773])).

fof(f773,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f772])).

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f774,plain,
    ( spl7_40
    | spl7_35
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f770,f457,f117,f329,f326,f727,f772])).

fof(f457,plain,
    ( spl7_19
  <=> ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | sK2 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f770,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(trivial_inequality_removal,[],[f769])).

fof(f769,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(superposition,[],[f748,f703])).

fof(f748,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) = k1_funct_1(sK3,sK4(sK2,X0)) )
    | ~ spl7_19 ),
    inference(resolution,[],[f458,f54])).

fof(f54,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f458,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | sK2 = X0 )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f457])).

fof(f701,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | spl7_19
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f700,f101,f457,f389,f386])).

fof(f700,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f58,f699])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f694,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f693,f104,f101])).

fof(f104,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f693,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f49,f687])).

fof(f687,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f50,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f663,plain,
    ( spl7_3
    | spl7_2 ),
    inference(avatar_split_clause,[],[f662,f104,f117])).

fof(f662,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(global_subsumption,[],[f52,f656])).

fof(f656,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f53,f73])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f643,plain,
    ( ~ spl7_2
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f633,f627])).

fof(f627,plain,
    ( r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f439,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f439,plain,
    ( r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f108,f433])).

fof(f433,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_7 ),
    inference(resolution,[],[f181,f358])).

fof(f358,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f172,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f172,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_7
  <=> ! [X1] : ~ r2_hidden(X1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f181,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f56,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f108,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f53,f90])).

fof(f633,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f600,f625])).

fof(f625,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(resolution,[],[f621,f181])).

fof(f621,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f200,f61])).

fof(f200,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl7_8
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f600,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f438,f105])).

fof(f438,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,k1_xboole_0)
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f55,f433])).

fof(f614,plain,
    ( ~ spl7_2
    | spl7_21 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | ~ spl7_2
    | spl7_21 ),
    inference(subsumption_resolution,[],[f56,f608])).

fof(f608,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_2
    | spl7_21 ),
    inference(forward_demodulation,[],[f603,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f603,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl7_2
    | spl7_21 ),
    inference(backward_demodulation,[],[f477,f105])).

fof(f477,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl7_21
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f478,plain,
    ( ~ spl7_21
    | spl7_8 ),
    inference(avatar_split_clause,[],[f473,f199,f476])).

fof(f473,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f430,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f430,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f98,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f98,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f50,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f399,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl7_16 ),
    inference(subsumption_resolution,[],[f48,f390])).

fof(f390,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f389])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f396,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | spl7_15 ),
    inference(subsumption_resolution,[],[f96,f387])).

fof(f387,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f386])).

fof(f96,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f339,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | spl7_13 ),
    inference(subsumption_resolution,[],[f51,f330])).

fof(f330,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f329])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f336,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl7_12 ),
    inference(subsumption_resolution,[],[f112,f327])).

fof(f327,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f326])).

fof(f112,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f71])).

fof(f179,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f56,f169])).

fof(f169,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f173,plain,
    ( ~ spl7_6
    | spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f165,f104,f171,f168])).

fof(f165,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f140,f60])).

fof(f140,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_2 ),
    inference(resolution,[],[f137,f62])).

fof(f137,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl7_2 ),
    inference(resolution,[],[f134,f65])).

fof(f134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f129,f82])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f53,f105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (15573)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (15575)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (15581)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (15578)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (15589)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (15577)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (15587)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (15574)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15572)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (15596)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (15595)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (15585)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (15593)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (15591)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (15588)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (15576)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (15583)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (15579)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (15598)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (15597)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (15592)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (15580)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (15590)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (15580)Refutation not found, incomplete strategy% (15580)------------------------------
% 0.21/0.54  % (15580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15580)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15580)Memory used [KB]: 10746
% 0.21/0.54  % (15580)Time elapsed: 0.139 s
% 0.21/0.54  % (15580)------------------------------
% 0.21/0.54  % (15580)------------------------------
% 0.21/0.54  % (15594)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (15582)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (15584)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (15582)Refutation not found, incomplete strategy% (15582)------------------------------
% 0.21/0.55  % (15582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15582)Memory used [KB]: 10746
% 0.21/0.55  % (15582)Time elapsed: 0.140 s
% 0.21/0.55  % (15582)------------------------------
% 0.21/0.55  % (15582)------------------------------
% 0.21/0.55  % (15600)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (15599)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (15586)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (15601)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.57  % (15574)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f815,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f173,f179,f336,f339,f396,f399,f478,f614,f643,f663,f694,f701,f774,f789,f814])).
% 1.52/0.57  fof(f814,plain,(
% 1.52/0.57    ~spl7_35),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f813])).
% 1.52/0.57  fof(f813,plain,(
% 1.52/0.57    $false | ~spl7_35),
% 1.52/0.57    inference(subsumption_resolution,[],[f92,f793])).
% 1.52/0.57  fof(f793,plain,(
% 1.52/0.57    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_35),
% 1.52/0.57    inference(backward_demodulation,[],[f55,f728])).
% 1.52/0.57  fof(f728,plain,(
% 1.52/0.57    sK2 = sK3 | ~spl7_35),
% 1.52/0.57    inference(avatar_component_clause,[],[f727])).
% 1.52/0.57  fof(f727,plain,(
% 1.52/0.57    spl7_35 <=> sK2 = sK3),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f31,f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.52/0.57    inference(flattening,[],[f16])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f15])).
% 1.52/0.57  fof(f15,negated_conjecture,(
% 1.52/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.52/0.57    inference(negated_conjecture,[],[f14])).
% 1.52/0.57  fof(f14,conjecture,(
% 1.52/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 1.52/0.57  fof(f92,plain,(
% 1.52/0.57    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.52/0.57    inference(resolution,[],[f50,f90])).
% 1.52/0.57  fof(f90,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f89])).
% 1.52/0.57  fof(f89,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.57    inference(equality_resolution,[],[f81])).
% 1.52/0.57  fof(f81,plain,(
% 1.52/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(nnf_transformation,[],[f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(flattening,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.52/0.57    inference(ennf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,axiom,(
% 1.52/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f789,plain,(
% 1.52/0.57    ~spl7_15 | ~spl7_16 | ~spl7_12 | ~spl7_13 | spl7_35 | ~spl7_1 | ~spl7_3 | ~spl7_40),
% 1.52/0.57    inference(avatar_split_clause,[],[f788,f772,f117,f101,f727,f329,f326,f389,f386])).
% 1.52/0.57  fof(f386,plain,(
% 1.52/0.57    spl7_15 <=> v1_relat_1(sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.52/0.57  fof(f389,plain,(
% 1.52/0.57    spl7_16 <=> v1_funct_1(sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.52/0.57  fof(f326,plain,(
% 1.52/0.57    spl7_12 <=> v1_relat_1(sK3)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.52/0.57  fof(f329,plain,(
% 1.52/0.57    spl7_13 <=> v1_funct_1(sK3)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.52/0.57  fof(f101,plain,(
% 1.52/0.57    spl7_1 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.52/0.57  fof(f117,plain,(
% 1.52/0.57    spl7_3 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.52/0.57  fof(f772,plain,(
% 1.52/0.57    spl7_40 <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.52/0.57  fof(f788,plain,(
% 1.52/0.57    sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_1 | ~spl7_3 | ~spl7_40)),
% 1.52/0.57    inference(trivial_inequality_removal,[],[f787])).
% 1.52/0.57  fof(f787,plain,(
% 1.52/0.57    sK0 != sK0 | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_1 | ~spl7_3 | ~spl7_40)),
% 1.52/0.57    inference(forward_demodulation,[],[f786,f699])).
% 1.52/0.57  fof(f699,plain,(
% 1.52/0.57    sK0 = k1_relat_1(sK2) | ~spl7_1),
% 1.52/0.57    inference(forward_demodulation,[],[f95,f102])).
% 1.52/0.57  fof(f102,plain,(
% 1.52/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f101])).
% 1.52/0.57  fof(f95,plain,(
% 1.52/0.57    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.52/0.57    inference(resolution,[],[f50,f72])).
% 1.52/0.57  fof(f72,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(ennf_transformation,[],[f11])).
% 1.52/0.57  fof(f11,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.52/0.57  fof(f786,plain,(
% 1.52/0.57    sK0 != k1_relat_1(sK2) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | ~spl7_40)),
% 1.52/0.57    inference(forward_demodulation,[],[f785,f703])).
% 1.52/0.57  fof(f703,plain,(
% 1.52/0.57    sK0 = k1_relat_1(sK3) | ~spl7_3),
% 1.52/0.57    inference(forward_demodulation,[],[f111,f118])).
% 1.52/0.57  fof(f118,plain,(
% 1.52/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_3),
% 1.52/0.57    inference(avatar_component_clause,[],[f117])).
% 1.52/0.57  fof(f111,plain,(
% 1.52/0.57    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.52/0.57    inference(resolution,[],[f53,f72])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f785,plain,(
% 1.52/0.57    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_40),
% 1.52/0.57    inference(trivial_inequality_removal,[],[f784])).
% 1.52/0.57  fof(f784,plain,(
% 1.52/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_40),
% 1.52/0.57    inference(superposition,[],[f59,f773])).
% 1.52/0.57  fof(f773,plain,(
% 1.52/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl7_40),
% 1.52/0.57    inference(avatar_component_clause,[],[f772])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f34])).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f33])).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f18])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.52/0.57  fof(f774,plain,(
% 1.52/0.57    spl7_40 | spl7_35 | ~spl7_12 | ~spl7_13 | ~spl7_3 | ~spl7_19),
% 1.52/0.57    inference(avatar_split_clause,[],[f770,f457,f117,f329,f326,f727,f772])).
% 1.52/0.57  fof(f457,plain,(
% 1.52/0.57    spl7_19 <=> ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK2 = X0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.52/0.57  fof(f770,plain,(
% 1.52/0.57    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_3 | ~spl7_19)),
% 1.52/0.57    inference(trivial_inequality_removal,[],[f769])).
% 1.52/0.57  fof(f769,plain,(
% 1.52/0.57    sK0 != sK0 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_3 | ~spl7_19)),
% 1.52/0.57    inference(superposition,[],[f748,f703])).
% 1.52/0.57  fof(f748,plain,(
% 1.52/0.57    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) = k1_funct_1(sK3,sK4(sK2,X0))) ) | ~spl7_19),
% 1.52/0.57    inference(resolution,[],[f458,f54])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f458,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK2 = X0) ) | ~spl7_19),
% 1.52/0.57    inference(avatar_component_clause,[],[f457])).
% 1.52/0.57  fof(f701,plain,(
% 1.52/0.57    ~spl7_15 | ~spl7_16 | spl7_19 | ~spl7_1),
% 1.52/0.57    inference(avatar_split_clause,[],[f700,f101,f457,f389,f386])).
% 1.52/0.57  fof(f700,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 1.52/0.57    inference(superposition,[],[f58,f699])).
% 1.52/0.57  fof(f58,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f34])).
% 1.52/0.57  fof(f694,plain,(
% 1.52/0.57    spl7_1 | spl7_2),
% 1.52/0.57    inference(avatar_split_clause,[],[f693,f104,f101])).
% 1.52/0.57  fof(f104,plain,(
% 1.52/0.57    spl7_2 <=> k1_xboole_0 = sK1),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.52/0.57  fof(f693,plain,(
% 1.52/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.52/0.57    inference(global_subsumption,[],[f49,f687])).
% 1.52/0.57  fof(f687,plain,(
% 1.52/0.57    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.52/0.57    inference(resolution,[],[f50,f73])).
% 1.52/0.57  fof(f73,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f46])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(nnf_transformation,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(flattening,[],[f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(ennf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f663,plain,(
% 1.52/0.57    spl7_3 | spl7_2),
% 1.52/0.57    inference(avatar_split_clause,[],[f662,f104,f117])).
% 1.52/0.57  fof(f662,plain,(
% 1.52/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.52/0.57    inference(global_subsumption,[],[f52,f656])).
% 1.52/0.57  fof(f656,plain,(
% 1.52/0.57    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.52/0.57    inference(resolution,[],[f53,f73])).
% 1.52/0.57  fof(f52,plain,(
% 1.52/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f643,plain,(
% 1.52/0.57    ~spl7_2 | ~spl7_7 | ~spl7_8),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f642])).
% 1.52/0.57  fof(f642,plain,(
% 1.52/0.57    $false | (~spl7_2 | ~spl7_7 | ~spl7_8)),
% 1.52/0.57    inference(subsumption_resolution,[],[f633,f627])).
% 1.52/0.57  fof(f627,plain,(
% 1.52/0.57    r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_2 | ~spl7_7)),
% 1.52/0.57    inference(forward_demodulation,[],[f439,f105])).
% 1.52/0.57  fof(f105,plain,(
% 1.52/0.57    k1_xboole_0 = sK1 | ~spl7_2),
% 1.52/0.57    inference(avatar_component_clause,[],[f104])).
% 1.52/0.57  fof(f439,plain,(
% 1.52/0.57    r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0) | ~spl7_7),
% 1.52/0.57    inference(backward_demodulation,[],[f108,f433])).
% 1.52/0.57  fof(f433,plain,(
% 1.52/0.57    k1_xboole_0 = sK3 | ~spl7_7),
% 1.52/0.57    inference(resolution,[],[f181,f358])).
% 1.52/0.57  fof(f358,plain,(
% 1.52/0.57    v1_xboole_0(sK3) | ~spl7_7),
% 1.52/0.57    inference(resolution,[],[f172,f61])).
% 1.52/0.57  fof(f61,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f38])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(rectify,[],[f35])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.52/0.57    inference(nnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.52/0.57  fof(f172,plain,(
% 1.52/0.57    ( ! [X1] : (~r2_hidden(X1,sK3)) ) | ~spl7_7),
% 1.52/0.57    inference(avatar_component_clause,[],[f171])).
% 1.52/0.57  fof(f171,plain,(
% 1.52/0.57    spl7_7 <=> ! [X1] : ~r2_hidden(X1,sK3)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.52/0.57  fof(f181,plain,(
% 1.52/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.52/0.57    inference(resolution,[],[f56,f70])).
% 1.52/0.57  fof(f70,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.52/0.57  fof(f56,plain,(
% 1.52/0.57    v1_xboole_0(k1_xboole_0)),
% 1.52/0.57    inference(cnf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    v1_xboole_0(k1_xboole_0)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.52/0.57  fof(f108,plain,(
% 1.52/0.57    r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.52/0.57    inference(resolution,[],[f53,f90])).
% 1.52/0.57  fof(f633,plain,(
% 1.52/0.57    ~r2_relset_1(sK0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_2 | ~spl7_7 | ~spl7_8)),
% 1.52/0.57    inference(backward_demodulation,[],[f600,f625])).
% 1.52/0.57  fof(f625,plain,(
% 1.52/0.57    k1_xboole_0 = sK2 | ~spl7_8),
% 1.52/0.57    inference(resolution,[],[f621,f181])).
% 1.52/0.57  fof(f621,plain,(
% 1.52/0.57    v1_xboole_0(sK2) | ~spl7_8),
% 1.52/0.57    inference(resolution,[],[f200,f61])).
% 1.52/0.57  fof(f200,plain,(
% 1.52/0.57    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl7_8),
% 1.52/0.57    inference(avatar_component_clause,[],[f199])).
% 1.52/0.57  fof(f199,plain,(
% 1.52/0.57    spl7_8 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.52/0.57  fof(f600,plain,(
% 1.52/0.57    ~r2_relset_1(sK0,k1_xboole_0,sK2,k1_xboole_0) | (~spl7_2 | ~spl7_7)),
% 1.52/0.57    inference(backward_demodulation,[],[f438,f105])).
% 1.52/0.57  fof(f438,plain,(
% 1.52/0.57    ~r2_relset_1(sK0,sK1,sK2,k1_xboole_0) | ~spl7_7),
% 1.52/0.57    inference(backward_demodulation,[],[f55,f433])).
% 1.52/0.57  fof(f614,plain,(
% 1.52/0.57    ~spl7_2 | spl7_21),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f613])).
% 1.52/0.57  fof(f613,plain,(
% 1.52/0.57    $false | (~spl7_2 | spl7_21)),
% 1.52/0.57    inference(subsumption_resolution,[],[f56,f608])).
% 1.52/0.57  fof(f608,plain,(
% 1.52/0.57    ~v1_xboole_0(k1_xboole_0) | (~spl7_2 | spl7_21)),
% 1.52/0.57    inference(forward_demodulation,[],[f603,f82])).
% 1.52/0.57  fof(f82,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f69])).
% 1.52/0.57  fof(f69,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f45])).
% 1.52/0.57  fof(f45,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.52/0.57    inference(flattening,[],[f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.52/0.57    inference(nnf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.52/0.57  fof(f603,plain,(
% 1.52/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl7_2 | spl7_21)),
% 1.52/0.57    inference(backward_demodulation,[],[f477,f105])).
% 1.52/0.57  fof(f477,plain,(
% 1.52/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl7_21),
% 1.52/0.57    inference(avatar_component_clause,[],[f476])).
% 1.52/0.57  fof(f476,plain,(
% 1.52/0.57    spl7_21 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.52/0.57  fof(f478,plain,(
% 1.52/0.57    ~spl7_21 | spl7_8),
% 1.52/0.57    inference(avatar_split_clause,[],[f473,f199,f476])).
% 1.52/0.57  fof(f473,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) )),
% 1.52/0.57    inference(resolution,[],[f430,f60])).
% 1.52/0.57  fof(f60,plain,(
% 1.52/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f38])).
% 1.52/0.57  fof(f430,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 1.52/0.57    inference(resolution,[],[f98,f62])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(rectify,[],[f39])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.57    inference(nnf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.57  fof(f98,plain,(
% 1.52/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.52/0.57    inference(resolution,[],[f50,f65])).
% 1.52/0.57  fof(f65,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f43])).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.52/0.57    inference(nnf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,axiom,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.52/0.57  fof(f399,plain,(
% 1.52/0.57    spl7_16),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f398])).
% 1.52/0.57  fof(f398,plain,(
% 1.52/0.57    $false | spl7_16),
% 1.52/0.57    inference(subsumption_resolution,[],[f48,f390])).
% 1.52/0.57  fof(f390,plain,(
% 1.52/0.57    ~v1_funct_1(sK2) | spl7_16),
% 1.52/0.57    inference(avatar_component_clause,[],[f389])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    v1_funct_1(sK2)),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f396,plain,(
% 1.52/0.57    spl7_15),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f395])).
% 1.52/0.57  fof(f395,plain,(
% 1.52/0.57    $false | spl7_15),
% 1.52/0.57    inference(subsumption_resolution,[],[f96,f387])).
% 1.52/0.57  fof(f387,plain,(
% 1.52/0.57    ~v1_relat_1(sK2) | spl7_15),
% 1.52/0.57    inference(avatar_component_clause,[],[f386])).
% 1.52/0.57  fof(f96,plain,(
% 1.52/0.57    v1_relat_1(sK2)),
% 1.52/0.57    inference(resolution,[],[f50,f71])).
% 1.52/0.57  fof(f71,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f22])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.52/0.57  fof(f339,plain,(
% 1.52/0.57    spl7_13),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f338])).
% 1.52/0.57  fof(f338,plain,(
% 1.52/0.57    $false | spl7_13),
% 1.52/0.57    inference(subsumption_resolution,[],[f51,f330])).
% 1.52/0.57  fof(f330,plain,(
% 1.52/0.57    ~v1_funct_1(sK3) | spl7_13),
% 1.52/0.57    inference(avatar_component_clause,[],[f329])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    v1_funct_1(sK3)),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f336,plain,(
% 1.52/0.57    spl7_12),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f335])).
% 1.52/0.57  fof(f335,plain,(
% 1.52/0.57    $false | spl7_12),
% 1.52/0.57    inference(subsumption_resolution,[],[f112,f327])).
% 1.52/0.57  fof(f327,plain,(
% 1.52/0.57    ~v1_relat_1(sK3) | spl7_12),
% 1.52/0.57    inference(avatar_component_clause,[],[f326])).
% 1.52/0.57  fof(f112,plain,(
% 1.52/0.57    v1_relat_1(sK3)),
% 1.52/0.57    inference(resolution,[],[f53,f71])).
% 1.52/0.57  fof(f179,plain,(
% 1.52/0.57    spl7_6),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f178])).
% 1.52/0.57  fof(f178,plain,(
% 1.52/0.57    $false | spl7_6),
% 1.52/0.57    inference(subsumption_resolution,[],[f56,f169])).
% 1.52/0.57  fof(f169,plain,(
% 1.52/0.57    ~v1_xboole_0(k1_xboole_0) | spl7_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f168])).
% 1.52/0.57  fof(f168,plain,(
% 1.52/0.57    spl7_6 <=> v1_xboole_0(k1_xboole_0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.52/0.57  fof(f173,plain,(
% 1.52/0.57    ~spl7_6 | spl7_7 | ~spl7_2),
% 1.52/0.57    inference(avatar_split_clause,[],[f165,f104,f171,f168])).
% 1.52/0.57  fof(f165,plain,(
% 1.52/0.57    ( ! [X1] : (~r2_hidden(X1,sK3) | ~v1_xboole_0(k1_xboole_0)) ) | ~spl7_2),
% 1.52/0.57    inference(resolution,[],[f140,f60])).
% 1.52/0.57  fof(f140,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,sK3)) ) | ~spl7_2),
% 1.52/0.57    inference(resolution,[],[f137,f62])).
% 1.52/0.57  fof(f137,plain,(
% 1.52/0.57    r1_tarski(sK3,k1_xboole_0) | ~spl7_2),
% 1.52/0.57    inference(resolution,[],[f134,f65])).
% 1.52/0.57  fof(f134,plain,(
% 1.52/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_2),
% 1.52/0.57    inference(forward_demodulation,[],[f129,f82])).
% 1.52/0.57  fof(f129,plain,(
% 1.52/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_2),
% 1.52/0.57    inference(backward_demodulation,[],[f53,f105])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (15574)------------------------------
% 1.52/0.57  % (15574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (15574)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (15574)Memory used [KB]: 11129
% 1.52/0.57  % (15574)Time elapsed: 0.164 s
% 1.52/0.57  % (15574)------------------------------
% 1.52/0.57  % (15574)------------------------------
% 1.52/0.58  % (15571)Success in time 0.218 s
%------------------------------------------------------------------------------
