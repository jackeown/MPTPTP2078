%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:28 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 432 expanded)
%              Number of leaves         :   19 ( 133 expanded)
%              Depth                    :   19
%              Number of atoms          :  372 (2249 expanded)
%              Number of equality atoms :   88 ( 402 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f147,f197,f243,f313])).

fof(f313,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f311,f268])).

fof(f268,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK0)
    | ~ spl9_1 ),
    inference(backward_demodulation,[],[f128,f267])).

fof(f267,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl9_1 ),
    inference(backward_demodulation,[],[f102,f110])).

fof(f110,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl9_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f102,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f57,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f128,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f124,f116])).

fof(f116,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f103,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f103,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f57,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f124,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f105,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f105,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f58,f99])).

fof(f99,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f57,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f58,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f311,plain,(
    ~ r2_hidden(sK8(sK4,sK2,sK3),sK0) ),
    inference(resolution,[],[f310,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f310,plain,(
    ~ m1_subset_1(sK8(sK4,sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f309,f130])).

fof(f130,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f126,f116])).

fof(f126,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f105,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f309,plain,
    ( ~ r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK8(sK4,sK2,sK3),sK0) ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ m1_subset_1(sK8(sK4,sK2,sK3),sK0) ),
    inference(superposition,[],[f59,f292])).

fof(f292,plain,(
    sK4 = k1_funct_1(sK3,sK8(sK4,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f291,f116])).

fof(f291,plain,
    ( sK4 = k1_funct_1(sK3,sK8(sK4,sK2,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f286,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f286,plain,
    ( sK4 = k1_funct_1(sK3,sK8(sK4,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f129,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f129,plain,(
    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f125,f116])).

fof(f125,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f105,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f59,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f243,plain,
    ( ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f241,f60])).

% (32630)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f241,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f228,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f228,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),k1_xboole_0)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f128,f227])).

fof(f227,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f205,f224])).

fof(f224,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f215,f207])).

fof(f207,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f121,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f121,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f56,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f56,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f215,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f208,f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f208,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f122,f146])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f57,f114])).

fof(f205,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f119,f146])).

fof(f119,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f102,f114])).

fof(f197,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f192,f60])).

fof(f192,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_3 ),
    inference(resolution,[],[f160,f63])).

% (32619)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (32629)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (32621)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f160,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0)
    | ~ spl9_3 ),
    inference(backward_demodulation,[],[f129,f142])).

fof(f142,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl9_3
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f147,plain,
    ( spl9_3
    | spl9_4
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f138,f112,f144,f140])).

fof(f138,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f131,f121])).

fof(f131,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl9_2 ),
    inference(resolution,[],[f122,f95])).

fof(f95,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f106,f112,f108])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f100,f56])).

fof(f100,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:51:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (32616)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (32611)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.49  % (32616)Refutation not found, incomplete strategy% (32616)------------------------------
% 0.21/0.49  % (32616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32616)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32616)Memory used [KB]: 10746
% 0.21/0.51  % (32616)Time elapsed: 0.081 s
% 0.21/0.51  % (32616)------------------------------
% 0.21/0.51  % (32616)------------------------------
% 0.21/0.51  % (32628)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (32607)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (32620)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (32608)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32610)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (32615)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (32617)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (32614)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (32617)Refutation not found, incomplete strategy% (32617)------------------------------
% 0.21/0.53  % (32617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32617)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32617)Memory used [KB]: 10746
% 0.21/0.53  % (32617)Time elapsed: 0.096 s
% 0.21/0.53  % (32617)------------------------------
% 0.21/0.53  % (32617)------------------------------
% 0.21/0.53  % (32634)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (32628)Refutation not found, incomplete strategy% (32628)------------------------------
% 0.21/0.53  % (32628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32628)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32628)Memory used [KB]: 10746
% 0.21/0.53  % (32628)Time elapsed: 0.106 s
% 0.21/0.53  % (32628)------------------------------
% 0.21/0.53  % (32628)------------------------------
% 0.21/0.53  % (32618)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (32625)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (32624)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (32633)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32632)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (32608)Refutation not found, incomplete strategy% (32608)------------------------------
% 0.21/0.54  % (32608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32609)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (32635)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (32606)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.55  % (32631)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.55  % (32623)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.55  % (32612)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.55  % (32626)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.56  % (32627)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.56  % (32614)Refutation found. Thanks to Tanya!
% 1.32/0.56  % SZS status Theorem for theBenchmark
% 1.32/0.56  % SZS output start Proof for theBenchmark
% 1.32/0.56  fof(f314,plain,(
% 1.32/0.56    $false),
% 1.32/0.56    inference(avatar_sat_refutation,[],[f115,f147,f197,f243,f313])).
% 1.32/0.56  fof(f313,plain,(
% 1.32/0.56    ~spl9_1),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f312])).
% 1.32/0.56  fof(f312,plain,(
% 1.32/0.56    $false | ~spl9_1),
% 1.32/0.56    inference(subsumption_resolution,[],[f311,f268])).
% 1.32/0.56  fof(f268,plain,(
% 1.32/0.56    r2_hidden(sK8(sK4,sK2,sK3),sK0) | ~spl9_1),
% 1.32/0.56    inference(backward_demodulation,[],[f128,f267])).
% 1.32/0.56  fof(f267,plain,(
% 1.32/0.56    sK0 = k1_relat_1(sK3) | ~spl9_1),
% 1.32/0.56    inference(backward_demodulation,[],[f102,f110])).
% 1.32/0.56  fof(f110,plain,(
% 1.32/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl9_1),
% 1.32/0.56    inference(avatar_component_clause,[],[f108])).
% 1.32/0.56  fof(f108,plain,(
% 1.32/0.56    spl9_1 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.32/0.56  fof(f102,plain,(
% 1.32/0.56    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.32/0.56    inference(resolution,[],[f57,f80])).
% 1.32/0.56  fof(f80,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f27])).
% 1.32/0.56  fof(f27,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.56    inference(ennf_transformation,[],[f13])).
% 1.32/0.56  fof(f13,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.32/0.56  fof(f57,plain,(
% 1.32/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.32/0.56    inference(cnf_transformation,[],[f35])).
% 1.32/0.56  fof(f35,plain,(
% 1.32/0.56    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f34,f33])).
% 1.32/0.56  fof(f33,plain,(
% 1.32/0.56    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f34,plain,(
% 1.32/0.56    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f19,plain,(
% 1.32/0.56    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.32/0.56    inference(flattening,[],[f18])).
% 1.32/0.56  fof(f18,plain,(
% 1.32/0.56    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.32/0.56    inference(ennf_transformation,[],[f17])).
% 1.32/0.56  fof(f17,negated_conjecture,(
% 1.32/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.32/0.56    inference(negated_conjecture,[],[f16])).
% 1.32/0.56  fof(f16,conjecture,(
% 1.32/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 1.32/0.56  fof(f128,plain,(
% 1.32/0.56    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.32/0.56    inference(subsumption_resolution,[],[f124,f116])).
% 1.32/0.56  fof(f116,plain,(
% 1.32/0.56    v1_relat_1(sK3)),
% 1.32/0.56    inference(subsumption_resolution,[],[f103,f65])).
% 1.32/0.56  fof(f65,plain,(
% 1.32/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f10])).
% 1.32/0.56  fof(f10,axiom,(
% 1.32/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.32/0.56  fof(f103,plain,(
% 1.32/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.32/0.56    inference(resolution,[],[f57,f62])).
% 1.32/0.56  fof(f62,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f20])).
% 1.32/0.56  fof(f20,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f9])).
% 1.32/0.56  fof(f9,axiom,(
% 1.32/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.32/0.56  fof(f124,plain,(
% 1.32/0.56    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.32/0.56    inference(resolution,[],[f105,f76])).
% 1.32/0.56  fof(f76,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f51])).
% 1.32/0.56  fof(f51,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).
% 1.32/0.56  fof(f50,plain,(
% 1.32/0.56    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f49,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.32/0.56    inference(rectify,[],[f48])).
% 1.32/0.56  fof(f48,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.32/0.56    inference(nnf_transformation,[],[f26])).
% 1.32/0.56  fof(f26,plain,(
% 1.32/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.32/0.56    inference(ennf_transformation,[],[f11])).
% 1.32/0.56  fof(f11,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.32/0.56  fof(f105,plain,(
% 1.32/0.56    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.32/0.56    inference(backward_demodulation,[],[f58,f99])).
% 1.32/0.56  fof(f99,plain,(
% 1.32/0.56    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.32/0.56    inference(resolution,[],[f57,f90])).
% 1.32/0.56  fof(f90,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f32])).
% 1.32/0.56  fof(f32,plain,(
% 1.32/0.56    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.56    inference(ennf_transformation,[],[f14])).
% 1.32/0.56  fof(f14,axiom,(
% 1.32/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.32/0.56  fof(f58,plain,(
% 1.32/0.56    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.32/0.56    inference(cnf_transformation,[],[f35])).
% 1.32/0.56  fof(f311,plain,(
% 1.32/0.56    ~r2_hidden(sK8(sK4,sK2,sK3),sK0)),
% 1.32/0.56    inference(resolution,[],[f310,f67])).
% 1.32/0.56  fof(f67,plain,(
% 1.32/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f22])).
% 1.32/0.56  fof(f22,plain,(
% 1.32/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.32/0.56    inference(ennf_transformation,[],[f7])).
% 1.32/0.56  fof(f7,axiom,(
% 1.32/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.32/0.56  fof(f310,plain,(
% 1.32/0.56    ~m1_subset_1(sK8(sK4,sK2,sK3),sK0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f309,f130])).
% 1.32/0.56  fof(f130,plain,(
% 1.32/0.56    r2_hidden(sK8(sK4,sK2,sK3),sK2)),
% 1.32/0.56    inference(subsumption_resolution,[],[f126,f116])).
% 1.32/0.56  fof(f126,plain,(
% 1.32/0.56    r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 1.32/0.56    inference(resolution,[],[f105,f78])).
% 1.32/0.56  fof(f78,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f51])).
% 1.32/0.56  fof(f309,plain,(
% 1.32/0.56    ~r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK8(sK4,sK2,sK3),sK0)),
% 1.32/0.56    inference(trivial_inequality_removal,[],[f308])).
% 1.32/0.56  fof(f308,plain,(
% 1.32/0.56    sK4 != sK4 | ~r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~m1_subset_1(sK8(sK4,sK2,sK3),sK0)),
% 1.32/0.56    inference(superposition,[],[f59,f292])).
% 1.32/0.56  fof(f292,plain,(
% 1.32/0.56    sK4 = k1_funct_1(sK3,sK8(sK4,sK2,sK3))),
% 1.32/0.56    inference(subsumption_resolution,[],[f291,f116])).
% 1.32/0.56  fof(f291,plain,(
% 1.32/0.56    sK4 = k1_funct_1(sK3,sK8(sK4,sK2,sK3)) | ~v1_relat_1(sK3)),
% 1.32/0.56    inference(subsumption_resolution,[],[f286,f55])).
% 1.32/0.56  fof(f55,plain,(
% 1.32/0.56    v1_funct_1(sK3)),
% 1.32/0.56    inference(cnf_transformation,[],[f35])).
% 1.32/0.56  fof(f286,plain,(
% 1.32/0.56    sK4 = k1_funct_1(sK3,sK8(sK4,sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.32/0.56    inference(resolution,[],[f129,f88])).
% 1.32/0.56  fof(f88,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f54])).
% 1.32/0.56  fof(f54,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.32/0.56    inference(flattening,[],[f53])).
% 1.32/0.56  fof(f53,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.32/0.56    inference(nnf_transformation,[],[f31])).
% 1.32/0.56  fof(f31,plain,(
% 1.32/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.32/0.56    inference(flattening,[],[f30])).
% 1.32/0.56  fof(f30,plain,(
% 1.32/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.32/0.56    inference(ennf_transformation,[],[f12])).
% 1.32/0.56  fof(f12,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.32/0.56  fof(f129,plain,(
% 1.32/0.56    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)),
% 1.32/0.56    inference(subsumption_resolution,[],[f125,f116])).
% 1.32/0.56  fof(f125,plain,(
% 1.32/0.56    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 1.32/0.56    inference(resolution,[],[f105,f77])).
% 1.32/0.56  fof(f77,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f51])).
% 1.32/0.56  fof(f59,plain,(
% 1.32/0.56    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f35])).
% 1.32/0.56  fof(f243,plain,(
% 1.32/0.56    ~spl9_2 | ~spl9_4),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f242])).
% 1.32/0.56  fof(f242,plain,(
% 1.32/0.56    $false | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(subsumption_resolution,[],[f241,f60])).
% 1.32/0.56  % (32630)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.56  fof(f60,plain,(
% 1.32/0.56    v1_xboole_0(k1_xboole_0)),
% 1.32/0.56    inference(cnf_transformation,[],[f3])).
% 1.32/0.56  fof(f3,axiom,(
% 1.32/0.56    v1_xboole_0(k1_xboole_0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.32/0.56  fof(f241,plain,(
% 1.32/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(resolution,[],[f228,f63])).
% 1.32/0.56  fof(f63,plain,(
% 1.32/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f39])).
% 1.32/0.56  fof(f39,plain,(
% 1.32/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.32/0.56  fof(f38,plain,(
% 1.32/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 1.32/0.56    introduced(choice_axiom,[])).
% 1.32/0.56  fof(f37,plain,(
% 1.32/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.56    inference(rectify,[],[f36])).
% 1.32/0.56  fof(f36,plain,(
% 1.32/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.32/0.56    inference(nnf_transformation,[],[f1])).
% 1.32/0.56  fof(f1,axiom,(
% 1.32/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.32/0.56  fof(f228,plain,(
% 1.32/0.56    r2_hidden(sK8(sK4,sK2,sK3),k1_xboole_0) | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(backward_demodulation,[],[f128,f227])).
% 1.32/0.56  fof(f227,plain,(
% 1.32/0.56    k1_xboole_0 = k1_relat_1(sK3) | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(backward_demodulation,[],[f205,f224])).
% 1.32/0.56  fof(f224,plain,(
% 1.32/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(subsumption_resolution,[],[f215,f207])).
% 1.32/0.56  fof(f207,plain,(
% 1.32/0.56    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(backward_demodulation,[],[f121,f146])).
% 1.32/0.56  fof(f146,plain,(
% 1.32/0.56    k1_xboole_0 = sK0 | ~spl9_4),
% 1.32/0.56    inference(avatar_component_clause,[],[f144])).
% 1.32/0.56  fof(f144,plain,(
% 1.32/0.56    spl9_4 <=> k1_xboole_0 = sK0),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.32/0.56  fof(f121,plain,(
% 1.32/0.56    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl9_2),
% 1.32/0.56    inference(backward_demodulation,[],[f56,f114])).
% 1.32/0.56  fof(f114,plain,(
% 1.32/0.56    k1_xboole_0 = sK1 | ~spl9_2),
% 1.32/0.56    inference(avatar_component_clause,[],[f112])).
% 1.32/0.56  fof(f112,plain,(
% 1.32/0.56    spl9_2 <=> k1_xboole_0 = sK1),
% 1.32/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.32/0.56  fof(f56,plain,(
% 1.32/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.32/0.56    inference(cnf_transformation,[],[f35])).
% 1.32/0.56  fof(f215,plain,(
% 1.32/0.56    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(resolution,[],[f208,f97])).
% 1.32/0.56  fof(f97,plain,(
% 1.32/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.32/0.56    inference(equality_resolution,[],[f82])).
% 1.32/0.56  fof(f82,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f52])).
% 1.32/0.56  fof(f52,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.56    inference(nnf_transformation,[],[f29])).
% 1.32/0.56  fof(f29,plain,(
% 1.32/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.56    inference(flattening,[],[f28])).
% 1.32/0.56  fof(f28,plain,(
% 1.32/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.56    inference(ennf_transformation,[],[f15])).
% 1.32/0.56  fof(f15,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.32/0.56  fof(f208,plain,(
% 1.32/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(backward_demodulation,[],[f122,f146])).
% 1.32/0.56  fof(f122,plain,(
% 1.32/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl9_2),
% 1.32/0.56    inference(backward_demodulation,[],[f57,f114])).
% 1.32/0.56  fof(f205,plain,(
% 1.32/0.56    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl9_2 | ~spl9_4)),
% 1.32/0.56    inference(backward_demodulation,[],[f119,f146])).
% 1.32/0.56  fof(f119,plain,(
% 1.32/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl9_2),
% 1.32/0.56    inference(backward_demodulation,[],[f102,f114])).
% 1.32/0.56  fof(f197,plain,(
% 1.32/0.56    ~spl9_3),
% 1.32/0.56    inference(avatar_contradiction_clause,[],[f196])).
% 1.32/0.56  fof(f196,plain,(
% 1.32/0.56    $false | ~spl9_3),
% 1.32/0.56    inference(subsumption_resolution,[],[f192,f60])).
% 1.32/0.56  fof(f192,plain,(
% 1.32/0.56    ~v1_xboole_0(k1_xboole_0) | ~spl9_3),
% 1.32/0.56    inference(resolution,[],[f160,f63])).
% 1.32/0.56  % (32619)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.32/0.56  % (32629)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.56  % (32621)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.57  fof(f160,plain,(
% 1.32/0.57    r2_hidden(k4_tarski(sK8(sK4,sK2,k1_xboole_0),sK4),k1_xboole_0) | ~spl9_3),
% 1.32/0.57    inference(backward_demodulation,[],[f129,f142])).
% 1.32/0.57  fof(f142,plain,(
% 1.32/0.57    k1_xboole_0 = sK3 | ~spl9_3),
% 1.32/0.57    inference(avatar_component_clause,[],[f140])).
% 1.32/0.57  fof(f140,plain,(
% 1.32/0.57    spl9_3 <=> k1_xboole_0 = sK3),
% 1.32/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.32/0.57  fof(f147,plain,(
% 1.32/0.57    spl9_3 | spl9_4 | ~spl9_2),
% 1.32/0.57    inference(avatar_split_clause,[],[f138,f112,f144,f140])).
% 1.32/0.57  fof(f138,plain,(
% 1.32/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl9_2),
% 1.32/0.57    inference(subsumption_resolution,[],[f131,f121])).
% 1.32/0.57  fof(f131,plain,(
% 1.32/0.57    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl9_2),
% 1.32/0.57    inference(resolution,[],[f122,f95])).
% 1.32/0.57  fof(f95,plain,(
% 1.32/0.57    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.32/0.57    inference(equality_resolution,[],[f85])).
% 1.32/0.57  fof(f85,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f52])).
% 1.32/0.57  fof(f115,plain,(
% 1.32/0.57    spl9_1 | spl9_2),
% 1.32/0.57    inference(avatar_split_clause,[],[f106,f112,f108])).
% 1.32/0.57  fof(f106,plain,(
% 1.32/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.32/0.57    inference(subsumption_resolution,[],[f100,f56])).
% 1.32/0.57  fof(f100,plain,(
% 1.32/0.57    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.32/0.57    inference(resolution,[],[f57,f81])).
% 1.32/0.57  fof(f81,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f52])).
% 1.32/0.57  % SZS output end Proof for theBenchmark
% 1.32/0.57  % (32614)------------------------------
% 1.32/0.57  % (32614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (32614)Termination reason: Refutation
% 1.32/0.57  
% 1.32/0.57  % (32614)Memory used [KB]: 10746
% 1.32/0.57  % (32614)Time elapsed: 0.130 s
% 1.32/0.57  % (32614)------------------------------
% 1.32/0.57  % (32614)------------------------------
% 1.32/0.57  % (32608)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (32608)Memory used [KB]: 10874
% 1.32/0.57  % (32608)Time elapsed: 0.121 s
% 1.32/0.57  % (32608)------------------------------
% 1.32/0.57  % (32608)------------------------------
% 1.32/0.57  % (32605)Success in time 0.196 s
%------------------------------------------------------------------------------
