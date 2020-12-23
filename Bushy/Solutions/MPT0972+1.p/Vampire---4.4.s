%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t18_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:39 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 817 expanded)
%              Number of leaves         :   20 ( 259 expanded)
%              Depth                    :   19
%              Number of atoms          :  640 (5438 expanded)
%              Number of equality atoms :  184 (1042 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2489,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f260,f341,f342,f384,f845,f942,f1288,f1472,f2249,f2480,f2481,f2488])).

fof(f2488,plain,(
    ~ spl8_80 ),
    inference(avatar_contradiction_clause,[],[f2487])).

fof(f2487,plain,
    ( $false
    | ~ spl8_80 ),
    inference(subsumption_resolution,[],[f2486,f117])).

fof(f117,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f66,f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t18_funct_2.p',redefinition_r2_relset_1)).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f56,f55])).

fof(f55,plain,
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
              ( k1_funct_1(sK2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK3)
        & ! [X4] :
            ( k1_funct_1(sK3,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3,X0,X1)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t18_funct_2.p',t18_funct_2)).

fof(f2486,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_80 ),
    inference(forward_demodulation,[],[f71,f799])).

fof(f799,plain,
    ( sK2 = sK3
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f798])).

fof(f798,plain,
    ( spl8_80
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f71,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f2481,plain,
    ( spl8_80
    | spl8_196
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f2409,f204,f139,f2347,f798])).

fof(f2347,plain,
    ( spl8_196
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_196])])).

fof(f139,plain,
    ( spl8_4
  <=> k1_relset_1(sK0,sK1,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f204,plain,
    ( spl8_20
  <=> k1_relset_1(sK0,sK1,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f2409,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f2408,f1528])).

fof(f1528,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f111,f140])).

fof(f140,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f111,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f66,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t18_funct_2.p',redefinition_k1_relset_1)).

fof(f2408,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2))
    | sK2 = sK3
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f2407,f110])).

fof(f110,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t18_funct_2.p',cc1_relset_1)).

fof(f2407,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2))
    | sK2 = sK3
    | ~ v1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f2406,f64])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f2406,plain,
    ( r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2))
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(trivial_inequality_removal,[],[f2404])).

fof(f2404,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK2,sK3),k1_relat_1(sK2))
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(superposition,[],[f2185,f1528])).

fof(f2185,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f2184,f188])).

fof(f188,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f83])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f2184,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f2182,f67])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f2182,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK4(X0,sK3),k1_relat_1(X0))
        | sK3 = X0
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_20 ),
    inference(superposition,[],[f74,f2181])).

fof(f2181,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f189,f205])).

fof(f205,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f189,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f69,f84])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t18_funct_2.p',t9_funct_1)).

fof(f2480,plain,
    ( ~ spl8_4
    | ~ spl8_20
    | spl8_183
    | ~ spl8_196 ),
    inference(avatar_contradiction_clause,[],[f2479])).

fof(f2479,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_183
    | ~ spl8_196 ),
    inference(subsumption_resolution,[],[f2448,f117])).

fof(f2448,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_183
    | ~ spl8_196 ),
    inference(backward_demodulation,[],[f2421,f2248])).

fof(f2248,plain,
    ( ~ r2_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl8_183 ),
    inference(avatar_component_clause,[],[f2247])).

fof(f2247,plain,
    ( spl8_183
  <=> ~ r2_relset_1(sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_183])])).

fof(f2421,plain,
    ( sK2 = sK3
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_196 ),
    inference(subsumption_resolution,[],[f2420,f1528])).

fof(f2420,plain,
    ( k1_relat_1(sK2) != sK0
    | sK2 = sK3
    | ~ spl8_20
    | ~ spl8_196 ),
    inference(forward_demodulation,[],[f2419,f2181])).

fof(f2419,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl8_196 ),
    inference(subsumption_resolution,[],[f2418,f110])).

fof(f2418,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl8_196 ),
    inference(subsumption_resolution,[],[f2417,f64])).

fof(f2417,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_196 ),
    inference(subsumption_resolution,[],[f2416,f188])).

fof(f2416,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_196 ),
    inference(subsumption_resolution,[],[f2415,f67])).

fof(f2415,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_196 ),
    inference(trivial_inequality_removal,[],[f2414])).

fof(f2414,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_196 ),
    inference(superposition,[],[f75,f2351])).

fof(f2351,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl8_196 ),
    inference(resolution,[],[f2348,f70])).

fof(f70,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2348,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl8_196 ),
    inference(avatar_component_clause,[],[f2347])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2249,plain,
    ( ~ spl8_183
    | spl8_80 ),
    inference(avatar_split_clause,[],[f2241,f798,f2247])).

fof(f2241,plain,
    ( sK2 = sK3
    | ~ r2_relset_1(sK0,sK1,sK3,sK2) ),
    inference(resolution,[],[f114,f69])).

fof(f114,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | sK2 = X1
      | ~ r2_relset_1(sK0,sK1,X1,sK2) ) ),
    inference(resolution,[],[f66,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1472,plain,
    ( ~ spl8_26
    | ~ spl8_42 ),
    inference(avatar_contradiction_clause,[],[f1471])).

fof(f1471,plain,
    ( $false
    | ~ spl8_26
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f1462,f1400])).

fof(f1400,plain,
    ( ~ r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl8_26
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f1399,f253])).

fof(f253,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl8_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f1399,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,k1_xboole_0)
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f71,f383])).

fof(f383,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl8_42
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f1462,plain,
    ( r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl8_42 ),
    inference(resolution,[],[f1394,f108])).

fof(f1394,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f69,f383])).

fof(f1288,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f1287])).

fof(f1287,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f1274,f1036])).

fof(f1036,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f1022,f990])).

fof(f990,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f146,f439])).

fof(f439,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f65,f259])).

fof(f259,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl8_28
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f146,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1022,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(resolution,[],[f989,f102])).

fof(f102,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t18_funct_2.p',d1_funct_2)).

fof(f989,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f146,f437])).

fof(f437,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f66,f259])).

fof(f1274,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f984,f146])).

fof(f984,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl8_5
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f137,f259])).

fof(f137,plain,
    ( k1_relset_1(sK0,sK1,sK2) != sK0
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl8_5
  <=> k1_relset_1(sK0,sK1,sK2) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f942,plain,
    ( ~ spl8_4
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f941])).

fof(f941,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f933,f572])).

fof(f572,plain,
    ( r2_relset_1(k1_xboole_0,sK1,sK2,sK2)
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f117,f259])).

fof(f933,plain,
    ( ~ r2_relset_1(k1_xboole_0,sK1,sK2,sK2)
    | ~ spl8_4
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(backward_demodulation,[],[f922,f571])).

fof(f571,plain,
    ( ~ r2_relset_1(k1_xboole_0,sK1,sK2,sK3)
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f71,f259])).

fof(f922,plain,
    ( sK2 = sK3
    | ~ spl8_4
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f921,f679])).

fof(f679,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f669,f459])).

fof(f459,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f140,f259])).

fof(f669,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl8_28 ),
    inference(resolution,[],[f437,f84])).

fof(f921,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(forward_demodulation,[],[f920,f655])).

fof(f655,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f645,f494])).

fof(f494,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f481,f436])).

fof(f436,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f68,f259])).

fof(f68,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f481,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl8_28 ),
    inference(resolution,[],[f435,f102])).

fof(f435,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f69,f259])).

fof(f645,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_28 ),
    inference(resolution,[],[f435,f84])).

fof(f920,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f919,f188])).

fof(f919,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f918,f67])).

fof(f918,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f917,f110])).

fof(f917,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(subsumption_resolution,[],[f916,f64])).

fof(f916,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(trivial_inequality_removal,[],[f915])).

fof(f915,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(superposition,[],[f75,f901])).

fof(f901,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl8_28
    | ~ spl8_86 ),
    inference(resolution,[],[f573,f844])).

fof(f844,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | ~ spl8_86 ),
    inference(avatar_component_clause,[],[f843])).

fof(f843,plain,
    ( spl8_86
  <=> r2_hidden(sK4(sK3,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f573,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f70,f259])).

fof(f845,plain,
    ( spl8_80
    | spl8_86
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f838,f258,f139,f843,f798])).

fof(f838,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f837,f110])).

fof(f837,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f836,f64])).

fof(f836,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(trivial_inequality_removal,[],[f835])).

fof(f835,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK4(sK3,sK2),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_4
    | ~ spl8_28 ),
    inference(superposition,[],[f662,f679])).

fof(f662,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK3,X1),k1_xboole_0)
        | sK3 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f661,f655])).

fof(f661,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK3,X1),k1_relat_1(sK3))
        | sK3 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f660,f188])).

fof(f660,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK3,X1),k1_relat_1(sK3))
        | sK3 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f657,f67])).

fof(f657,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | r2_hidden(sK4(sK3,X1),k1_relat_1(sK3))
        | sK3 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_28 ),
    inference(superposition,[],[f74,f655])).

fof(f384,plain,
    ( spl8_42
    | spl8_28
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f377,f145,f258,f382])).

fof(f377,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f364,f345])).

fof(f345,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f146,f68])).

fof(f364,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl8_6 ),
    inference(resolution,[],[f346,f100])).

fof(f100,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f346,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f146,f69])).

fof(f342,plain,
    ( spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f287,f145,f139])).

fof(f287,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(subsumption_resolution,[],[f278,f65])).

fof(f278,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(resolution,[],[f66,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f341,plain,
    ( spl8_20
    | spl8_6 ),
    inference(avatar_split_clause,[],[f305,f145,f204])).

fof(f305,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(subsumption_resolution,[],[f296,f68])).

fof(f296,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(resolution,[],[f69,f86])).

fof(f260,plain,
    ( spl8_26
    | spl8_28
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f247,f145,f258,f252])).

fof(f247,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f234,f222])).

fof(f222,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f146,f65])).

fof(f234,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(resolution,[],[f223,f100])).

fof(f223,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f146,f66])).
%------------------------------------------------------------------------------
