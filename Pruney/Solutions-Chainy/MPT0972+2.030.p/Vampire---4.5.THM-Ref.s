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

% Result     : Theorem 0.22s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 376 expanded)
%              Number of leaves         :   28 ( 130 expanded)
%              Depth                    :   12
%              Number of atoms          :  500 (2157 expanded)
%              Number of equality atoms :  135 ( 407 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f157,f161,f234,f296,f299,f375,f377,f412,f431,f434,f467,f489,f511])).

fof(f511,plain,(
    ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f91,f493])).

fof(f493,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f54,f409])).

fof(f409,plain,
    ( sK2 = sK3
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl7_25
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f54,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

fof(f91,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f49,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f489,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_27
    | spl7_25
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f488,f465,f123,f100,f408,f423,f420,f276,f273])).

fof(f273,plain,
    ( spl7_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f276,plain,
    ( spl7_14
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f420,plain,
    ( spl7_26
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f423,plain,
    ( spl7_27
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f100,plain,
    ( spl7_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f123,plain,
    ( spl7_5
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f465,plain,
    ( spl7_32
  <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f488,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_32 ),
    inference(trivial_inequality_removal,[],[f487])).

fof(f487,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f486,f270])).

fof(f270,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f94,f101])).

fof(f101,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f94,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f49,f71])).

fof(f71,plain,(
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

fof(f486,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_5
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f485,f417])).

fof(f417,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f117,f124])).

fof(f124,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f117,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f52,f71])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f485,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_32 ),
    inference(trivial_inequality_removal,[],[f484])).

fof(f484,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_32 ),
    inference(superposition,[],[f59,f466])).

fof(f466,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f465])).

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f32])).

% (11941)Refutation not found, incomplete strategy% (11941)------------------------------
% (11941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11941)Termination reason: Refutation not found, incomplete strategy

% (11941)Memory used [KB]: 10746
% (11941)Time elapsed: 0.150 s
% (11941)------------------------------
% (11941)------------------------------
fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f467,plain,
    ( spl7_32
    | spl7_25
    | ~ spl7_26
    | ~ spl7_27
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f463,f279,f123,f423,f420,f408,f465])).

fof(f279,plain,
    ( spl7_15
  <=> ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | sK2 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f463,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(superposition,[],[f442,f417])).

fof(f442,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) = k1_funct_1(sK3,sK4(sK2,X0)) )
    | ~ spl7_15 ),
    inference(resolution,[],[f280,f53])).

fof(f53,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f280,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | sK2 = X0 )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f279])).

fof(f434,plain,(
    spl7_27 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl7_27 ),
    inference(subsumption_resolution,[],[f50,f424])).

fof(f424,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f423])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f431,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | spl7_26 ),
    inference(subsumption_resolution,[],[f118,f421])).

fof(f421,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f420])).

fof(f118,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f412,plain,
    ( spl7_5
    | spl7_2 ),
    inference(avatar_split_clause,[],[f411,f103,f123])).

fof(f103,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f411,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(global_subsumption,[],[f51,f398])).

fof(f398,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f377,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | spl7_15
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f376,f100,f279,f276,f273])).

fof(f376,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f58,f270])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f375,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f374,f103,f100])).

fof(f374,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f48,f368])).

fof(f368,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f49,f72])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f299,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl7_14 ),
    inference(subsumption_resolution,[],[f47,f277])).

fof(f277,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f276])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f296,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl7_13 ),
    inference(subsumption_resolution,[],[f95,f274])).

fof(f274,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f273])).

fof(f95,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f49,f70])).

fof(f234,plain,
    ( ~ spl7_3
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f228,f212])).

fof(f212,plain,
    ( r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f114,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_6 ),
    inference(resolution,[],[f171,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f171,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
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

fof(f128,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_6
  <=> ! [X1] : ~ r2_hidden(X1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f114,plain,(
    r2_relset_1(sK0,sK1,sK3,sK3) ),
    inference(resolution,[],[f52,f89])).

fof(f228,plain,
    ( ~ r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f227,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_3 ),
    inference(resolution,[],[f178,f57])).

fof(f178,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f108,f61])).

fof(f108,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_3
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f227,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,k1_xboole_0)
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f54,f172])).

fof(f161,plain,
    ( spl7_3
    | ~ spl7_9
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f159,f103,f153,f107])).

fof(f153,plain,
    ( spl7_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl7_2 ),
    inference(resolution,[],[f145,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f140,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f49,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f157,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl7_9 ),
    inference(subsumption_resolution,[],[f55,f154])).

fof(f154,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f155,plain,
    ( spl7_6
    | ~ spl7_9
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f150,f103,f153,f127])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_2 ),
    inference(resolution,[],[f144,f78])).

fof(f144,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f139,f81])).

fof(f139,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f52,f104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:43:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (11938)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (11943)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (11939)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (11947)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (11951)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (11939)Refutation not found, incomplete strategy% (11939)------------------------------
% 0.22/0.55  % (11939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11955)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (11933)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (11946)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (11957)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (11949)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (11954)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (11948)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (11934)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (11937)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (11935)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (11940)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (11959)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (11939)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (11939)Memory used [KB]: 10874
% 0.22/0.56  % (11939)Time elapsed: 0.109 s
% 0.22/0.56  % (11939)------------------------------
% 0.22/0.56  % (11939)------------------------------
% 0.22/0.56  % (11953)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (11948)Refutation not found, incomplete strategy% (11948)------------------------------
% 0.22/0.56  % (11948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (11956)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (11932)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (11958)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (11933)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (11941)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.57  % (11945)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.57  % (11942)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.57  % (11950)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.58  % (11944)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.58  % (11948)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (11948)Memory used [KB]: 10746
% 1.53/0.58  % (11948)Time elapsed: 0.134 s
% 1.53/0.58  % (11948)------------------------------
% 1.53/0.58  % (11948)------------------------------
% 1.53/0.58  % SZS output start Proof for theBenchmark
% 1.53/0.58  fof(f512,plain,(
% 1.53/0.58    $false),
% 1.53/0.58    inference(avatar_sat_refutation,[],[f155,f157,f161,f234,f296,f299,f375,f377,f412,f431,f434,f467,f489,f511])).
% 1.53/0.58  fof(f511,plain,(
% 1.53/0.58    ~spl7_25),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f510])).
% 1.53/0.58  fof(f510,plain,(
% 1.53/0.58    $false | ~spl7_25),
% 1.53/0.58    inference(subsumption_resolution,[],[f91,f493])).
% 1.53/0.58  fof(f493,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_25),
% 1.53/0.58    inference(backward_demodulation,[],[f54,f409])).
% 1.53/0.58  fof(f409,plain,(
% 1.53/0.58    sK2 = sK3 | ~spl7_25),
% 1.53/0.58    inference(avatar_component_clause,[],[f408])).
% 1.53/0.58  fof(f408,plain,(
% 1.53/0.58    spl7_25 <=> sK2 = sK3),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.53/0.58  fof(f54,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f30,f29])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f30,plain,(
% 1.53/0.58    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f17,plain,(
% 1.53/0.58    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/0.58    inference(flattening,[],[f16])).
% 1.53/0.58  fof(f16,plain,(
% 1.53/0.58    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.53/0.58    inference(ennf_transformation,[],[f15])).
% 1.53/0.58  fof(f15,negated_conjecture,(
% 1.53/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.53/0.58    inference(negated_conjecture,[],[f14])).
% 1.53/0.58  fof(f14,conjecture,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 1.53/0.58  fof(f91,plain,(
% 1.53/0.58    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.53/0.58    inference(resolution,[],[f49,f89])).
% 1.53/0.58  fof(f89,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f88])).
% 1.53/0.58  fof(f88,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.58    inference(equality_resolution,[],[f80])).
% 1.53/0.58  fof(f80,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f46])).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(nnf_transformation,[],[f28])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(flattening,[],[f27])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.53/0.58    inference(ennf_transformation,[],[f11])).
% 1.53/0.58  fof(f11,axiom,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f489,plain,(
% 1.53/0.58    ~spl7_13 | ~spl7_14 | ~spl7_26 | ~spl7_27 | spl7_25 | ~spl7_1 | ~spl7_5 | ~spl7_32),
% 1.53/0.58    inference(avatar_split_clause,[],[f488,f465,f123,f100,f408,f423,f420,f276,f273])).
% 1.53/0.58  fof(f273,plain,(
% 1.53/0.58    spl7_13 <=> v1_relat_1(sK2)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.53/0.58  fof(f276,plain,(
% 1.53/0.58    spl7_14 <=> v1_funct_1(sK2)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.53/0.58  fof(f420,plain,(
% 1.53/0.58    spl7_26 <=> v1_relat_1(sK3)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.53/0.58  fof(f423,plain,(
% 1.53/0.58    spl7_27 <=> v1_funct_1(sK3)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.53/0.58  fof(f100,plain,(
% 1.53/0.58    spl7_1 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.53/0.58  fof(f123,plain,(
% 1.53/0.58    spl7_5 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.53/0.58  fof(f465,plain,(
% 1.53/0.58    spl7_32 <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.53/0.58  fof(f488,plain,(
% 1.53/0.58    sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_1 | ~spl7_5 | ~spl7_32)),
% 1.53/0.58    inference(trivial_inequality_removal,[],[f487])).
% 1.53/0.58  fof(f487,plain,(
% 1.53/0.58    sK0 != sK0 | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_1 | ~spl7_5 | ~spl7_32)),
% 1.53/0.58    inference(forward_demodulation,[],[f486,f270])).
% 1.53/0.58  fof(f270,plain,(
% 1.53/0.58    sK0 = k1_relat_1(sK2) | ~spl7_1),
% 1.53/0.58    inference(forward_demodulation,[],[f94,f101])).
% 1.53/0.58  fof(f101,plain,(
% 1.53/0.58    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_1),
% 1.53/0.58    inference(avatar_component_clause,[],[f100])).
% 1.53/0.58  fof(f94,plain,(
% 1.53/0.58    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.53/0.58    inference(resolution,[],[f49,f71])).
% 1.53/0.58  fof(f71,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f23])).
% 1.53/0.58  fof(f23,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f10])).
% 1.53/0.58  fof(f10,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.53/0.58  fof(f486,plain,(
% 1.53/0.58    sK0 != k1_relat_1(sK2) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_5 | ~spl7_32)),
% 1.53/0.58    inference(forward_demodulation,[],[f485,f417])).
% 1.53/0.58  fof(f417,plain,(
% 1.53/0.58    sK0 = k1_relat_1(sK3) | ~spl7_5),
% 1.53/0.58    inference(forward_demodulation,[],[f117,f124])).
% 1.53/0.58  fof(f124,plain,(
% 1.53/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_5),
% 1.53/0.58    inference(avatar_component_clause,[],[f123])).
% 1.53/0.58  fof(f117,plain,(
% 1.53/0.58    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.53/0.58    inference(resolution,[],[f52,f71])).
% 1.53/0.58  fof(f52,plain,(
% 1.53/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f485,plain,(
% 1.53/0.58    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_32),
% 1.53/0.58    inference(trivial_inequality_removal,[],[f484])).
% 1.53/0.58  fof(f484,plain,(
% 1.53/0.58    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_32),
% 1.53/0.58    inference(superposition,[],[f59,f466])).
% 1.53/0.58  fof(f466,plain,(
% 1.53/0.58    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl7_32),
% 1.53/0.58    inference(avatar_component_clause,[],[f465])).
% 1.53/0.58  fof(f59,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f33])).
% 1.53/0.58  fof(f33,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f32])).
% 1.53/0.58  % (11941)Refutation not found, incomplete strategy% (11941)------------------------------
% 1.53/0.58  % (11941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (11941)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (11941)Memory used [KB]: 10746
% 1.53/0.58  % (11941)Time elapsed: 0.150 s
% 1.53/0.58  % (11941)------------------------------
% 1.53/0.58  % (11941)------------------------------
% 1.53/0.58  fof(f32,plain,(
% 1.53/0.58    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(flattening,[],[f19])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f8])).
% 1.53/0.58  fof(f8,axiom,(
% 1.53/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.53/0.58  fof(f467,plain,(
% 1.53/0.58    spl7_32 | spl7_25 | ~spl7_26 | ~spl7_27 | ~spl7_5 | ~spl7_15),
% 1.53/0.58    inference(avatar_split_clause,[],[f463,f279,f123,f423,f420,f408,f465])).
% 1.53/0.58  fof(f279,plain,(
% 1.53/0.58    spl7_15 <=> ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK2 = X0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.53/0.58  fof(f463,plain,(
% 1.53/0.58    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_5 | ~spl7_15)),
% 1.53/0.58    inference(trivial_inequality_removal,[],[f462])).
% 1.53/0.58  fof(f462,plain,(
% 1.53/0.58    sK0 != sK0 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_5 | ~spl7_15)),
% 1.53/0.58    inference(superposition,[],[f442,f417])).
% 1.53/0.58  fof(f442,plain,(
% 1.53/0.58    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) = k1_funct_1(sK3,sK4(sK2,X0))) ) | ~spl7_15),
% 1.53/0.58    inference(resolution,[],[f280,f53])).
% 1.53/0.58  fof(f53,plain,(
% 1.53/0.58    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f280,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK2 = X0) ) | ~spl7_15),
% 1.53/0.58    inference(avatar_component_clause,[],[f279])).
% 1.53/0.58  fof(f434,plain,(
% 1.53/0.58    spl7_27),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f433])).
% 1.53/0.58  fof(f433,plain,(
% 1.53/0.58    $false | spl7_27),
% 1.53/0.58    inference(subsumption_resolution,[],[f50,f424])).
% 1.53/0.58  fof(f424,plain,(
% 1.53/0.58    ~v1_funct_1(sK3) | spl7_27),
% 1.53/0.58    inference(avatar_component_clause,[],[f423])).
% 1.53/0.58  fof(f50,plain,(
% 1.53/0.58    v1_funct_1(sK3)),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f431,plain,(
% 1.53/0.58    spl7_26),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f430])).
% 1.53/0.58  fof(f430,plain,(
% 1.53/0.58    $false | spl7_26),
% 1.53/0.58    inference(subsumption_resolution,[],[f118,f421])).
% 1.53/0.58  fof(f421,plain,(
% 1.53/0.58    ~v1_relat_1(sK3) | spl7_26),
% 1.53/0.58    inference(avatar_component_clause,[],[f420])).
% 1.53/0.58  fof(f118,plain,(
% 1.53/0.58    v1_relat_1(sK3)),
% 1.53/0.58    inference(resolution,[],[f52,f70])).
% 1.53/0.58  fof(f70,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f22])).
% 1.53/0.58  fof(f22,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f9])).
% 1.53/0.58  fof(f9,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.53/0.58  fof(f412,plain,(
% 1.53/0.58    spl7_5 | spl7_2),
% 1.53/0.58    inference(avatar_split_clause,[],[f411,f103,f123])).
% 1.53/0.58  fof(f103,plain,(
% 1.53/0.58    spl7_2 <=> k1_xboole_0 = sK1),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.53/0.58  fof(f411,plain,(
% 1.53/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.53/0.58    inference(global_subsumption,[],[f51,f398])).
% 1.53/0.58  fof(f398,plain,(
% 1.53/0.58    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.53/0.58    inference(resolution,[],[f52,f72])).
% 1.53/0.58  fof(f72,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.53/0.58    inference(cnf_transformation,[],[f45])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(nnf_transformation,[],[f25])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(flattening,[],[f24])).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f13])).
% 1.53/0.58  fof(f13,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.53/0.58  fof(f51,plain,(
% 1.53/0.58    v1_funct_2(sK3,sK0,sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f377,plain,(
% 1.53/0.58    ~spl7_13 | ~spl7_14 | spl7_15 | ~spl7_1),
% 1.53/0.58    inference(avatar_split_clause,[],[f376,f100,f279,f276,f273])).
% 1.53/0.58  fof(f376,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 1.53/0.58    inference(superposition,[],[f58,f270])).
% 1.53/0.58  fof(f58,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f33])).
% 1.53/0.58  fof(f375,plain,(
% 1.53/0.58    spl7_1 | spl7_2),
% 1.53/0.58    inference(avatar_split_clause,[],[f374,f103,f100])).
% 1.53/0.58  fof(f374,plain,(
% 1.53/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.58    inference(global_subsumption,[],[f48,f368])).
% 1.53/0.58  fof(f368,plain,(
% 1.53/0.58    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.58    inference(resolution,[],[f49,f72])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f299,plain,(
% 1.53/0.58    spl7_14),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f298])).
% 1.53/0.58  fof(f298,plain,(
% 1.53/0.58    $false | spl7_14),
% 1.53/0.58    inference(subsumption_resolution,[],[f47,f277])).
% 1.53/0.58  fof(f277,plain,(
% 1.53/0.58    ~v1_funct_1(sK2) | spl7_14),
% 1.53/0.58    inference(avatar_component_clause,[],[f276])).
% 1.53/0.58  fof(f47,plain,(
% 1.53/0.58    v1_funct_1(sK2)),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f296,plain,(
% 1.53/0.58    spl7_13),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f295])).
% 1.53/0.58  fof(f295,plain,(
% 1.53/0.58    $false | spl7_13),
% 1.53/0.58    inference(subsumption_resolution,[],[f95,f274])).
% 1.53/0.58  fof(f274,plain,(
% 1.53/0.58    ~v1_relat_1(sK2) | spl7_13),
% 1.53/0.58    inference(avatar_component_clause,[],[f273])).
% 1.53/0.58  fof(f95,plain,(
% 1.53/0.58    v1_relat_1(sK2)),
% 1.53/0.58    inference(resolution,[],[f49,f70])).
% 1.53/0.58  fof(f234,plain,(
% 1.53/0.58    ~spl7_3 | ~spl7_6),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f233])).
% 1.53/0.58  fof(f233,plain,(
% 1.53/0.58    $false | (~spl7_3 | ~spl7_6)),
% 1.53/0.58    inference(subsumption_resolution,[],[f228,f212])).
% 1.53/0.58  fof(f212,plain,(
% 1.53/0.58    r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0) | ~spl7_6),
% 1.53/0.58    inference(forward_demodulation,[],[f114,f172])).
% 1.53/0.58  fof(f172,plain,(
% 1.53/0.58    k1_xboole_0 = sK3 | ~spl7_6),
% 1.53/0.58    inference(resolution,[],[f171,f57])).
% 1.53/0.58  fof(f57,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.53/0.58    inference(cnf_transformation,[],[f18])).
% 1.53/0.58  fof(f18,plain,(
% 1.53/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f4])).
% 1.53/0.58  fof(f4,axiom,(
% 1.53/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.53/0.58  fof(f171,plain,(
% 1.53/0.58    v1_xboole_0(sK3) | ~spl7_6),
% 1.53/0.58    inference(resolution,[],[f128,f61])).
% 1.53/0.58  fof(f61,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f37])).
% 1.53/0.58  fof(f37,plain,(
% 1.53/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f35,plain,(
% 1.53/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.53/0.58    inference(rectify,[],[f34])).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.53/0.58    inference(nnf_transformation,[],[f1])).
% 1.53/0.58  fof(f1,axiom,(
% 1.53/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.53/0.58  fof(f128,plain,(
% 1.53/0.58    ( ! [X1] : (~r2_hidden(X1,sK3)) ) | ~spl7_6),
% 1.53/0.58    inference(avatar_component_clause,[],[f127])).
% 1.53/0.58  fof(f127,plain,(
% 1.53/0.58    spl7_6 <=> ! [X1] : ~r2_hidden(X1,sK3)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.53/0.58  fof(f114,plain,(
% 1.53/0.58    r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.53/0.58    inference(resolution,[],[f52,f89])).
% 1.53/0.58  fof(f228,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0) | (~spl7_3 | ~spl7_6)),
% 1.53/0.58    inference(forward_demodulation,[],[f227,f180])).
% 1.53/0.58  fof(f180,plain,(
% 1.53/0.58    k1_xboole_0 = sK2 | ~spl7_3),
% 1.53/0.58    inference(resolution,[],[f178,f57])).
% 1.53/0.58  fof(f178,plain,(
% 1.53/0.58    v1_xboole_0(sK2) | ~spl7_3),
% 1.53/0.58    inference(resolution,[],[f108,f61])).
% 1.53/0.58  fof(f108,plain,(
% 1.53/0.58    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl7_3),
% 1.53/0.58    inference(avatar_component_clause,[],[f107])).
% 1.53/0.58  fof(f107,plain,(
% 1.53/0.58    spl7_3 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.53/0.58  fof(f227,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK1,sK2,k1_xboole_0) | ~spl7_6),
% 1.53/0.58    inference(forward_demodulation,[],[f54,f172])).
% 1.53/0.58  fof(f161,plain,(
% 1.53/0.58    spl7_3 | ~spl7_9 | ~spl7_2),
% 1.53/0.58    inference(avatar_split_clause,[],[f159,f103,f153,f107])).
% 1.53/0.58  fof(f153,plain,(
% 1.53/0.58    spl7_9 <=> v1_xboole_0(k1_xboole_0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.53/0.58  fof(f159,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X0,sK2)) ) | ~spl7_2),
% 1.53/0.58    inference(resolution,[],[f145,f78])).
% 1.53/0.58  fof(f78,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.53/0.58  fof(f145,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl7_2),
% 1.53/0.58    inference(forward_demodulation,[],[f140,f81])).
% 1.53/0.58  fof(f81,plain,(
% 1.53/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.53/0.58    inference(equality_resolution,[],[f69])).
% 1.53/0.58  fof(f69,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.53/0.58    inference(cnf_transformation,[],[f44])).
% 1.53/0.58  fof(f44,plain,(
% 1.53/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.53/0.58    inference(flattening,[],[f43])).
% 1.53/0.58  fof(f43,plain,(
% 1.53/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.53/0.58    inference(nnf_transformation,[],[f5])).
% 1.53/0.58  fof(f5,axiom,(
% 1.53/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.53/0.58  fof(f140,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_2),
% 1.53/0.58    inference(backward_demodulation,[],[f49,f104])).
% 1.53/0.58  fof(f104,plain,(
% 1.53/0.58    k1_xboole_0 = sK1 | ~spl7_2),
% 1.53/0.58    inference(avatar_component_clause,[],[f103])).
% 1.53/0.58  fof(f157,plain,(
% 1.53/0.58    spl7_9),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f156])).
% 1.53/0.58  fof(f156,plain,(
% 1.53/0.58    $false | spl7_9),
% 1.53/0.58    inference(subsumption_resolution,[],[f55,f154])).
% 1.53/0.58  fof(f154,plain,(
% 1.53/0.58    ~v1_xboole_0(k1_xboole_0) | spl7_9),
% 1.53/0.58    inference(avatar_component_clause,[],[f153])).
% 1.53/0.58  fof(f55,plain,(
% 1.53/0.58    v1_xboole_0(k1_xboole_0)),
% 1.53/0.58    inference(cnf_transformation,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    v1_xboole_0(k1_xboole_0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.53/0.58  fof(f155,plain,(
% 1.53/0.58    spl7_6 | ~spl7_9 | ~spl7_2),
% 1.53/0.58    inference(avatar_split_clause,[],[f150,f103,f153,f127])).
% 1.53/0.58  fof(f150,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X0,sK3)) ) | ~spl7_2),
% 1.53/0.58    inference(resolution,[],[f144,f78])).
% 1.53/0.58  fof(f144,plain,(
% 1.53/0.58    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_2),
% 1.53/0.58    inference(forward_demodulation,[],[f139,f81])).
% 1.53/0.58  fof(f139,plain,(
% 1.53/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_2),
% 1.53/0.58    inference(backward_demodulation,[],[f52,f104])).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (11933)------------------------------
% 1.53/0.58  % (11933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (11933)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (11933)Memory used [KB]: 11001
% 1.53/0.58  % (11933)Time elapsed: 0.139 s
% 1.53/0.58  % (11933)------------------------------
% 1.53/0.58  % (11933)------------------------------
% 1.53/0.58  % (11952)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.53/0.58  % (11930)Success in time 0.208 s
%------------------------------------------------------------------------------
