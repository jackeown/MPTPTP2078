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
% DateTime   : Thu Dec  3 13:01:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 467 expanded)
%              Number of leaves         :   22 ( 131 expanded)
%              Depth                    :   20
%              Number of atoms          :  485 (2411 expanded)
%              Number of equality atoms :  109 ( 513 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f426,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f101,f125,f141,f224,f329,f425])).

fof(f425,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f423,f81])).

fof(f81,plain,(
    r2_hidden(sK2,k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f80,f39])).

% (14191)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ! [X4] :
        ( sK2 != k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK2 != k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (14190)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f80,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f40,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f423,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f422,f414])).

fof(f414,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK0)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f404,f77])).

fof(f77,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f75,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f75,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f44,f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f404,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(superposition,[],[f43,f397])).

fof(f397,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f393,f39])).

fof(f393,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(superposition,[],[f121,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f121,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f43,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f422,plain,(
    ~ r2_hidden(sK2,k9_relat_1(sK3,sK0)) ),
    inference(subsumption_resolution,[],[f421,f77])).

fof(f421,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(sK3,sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f420,f37])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f420,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(duplicate_literal_removal,[],[f419])).

fof(f419,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(sK3,sK0))
    | ~ r2_hidden(sK2,k9_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f114,f68])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
                  & r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
                    & r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
        & r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK3,X0,sK2),sK0)
      | ~ r2_hidden(sK2,k9_relat_1(sK3,X0)) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( sK2 != X1
      | ~ r2_hidden(sK6(sK3,X0,X1),sK0)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f107,f77])).

fof(f107,plain,(
    ! [X0,X1] :
      ( sK2 != X1
      | ~ r2_hidden(sK6(sK3,X0,X1),sK0)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f106,f37])).

fof(f106,plain,(
    ! [X0,X1] :
      ( sK2 != X1
      | ~ r2_hidden(sK6(sK3,X0,X1),sK0)
      | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f41,f67])).

fof(f67,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f41,plain,(
    ! [X4] :
      ( sK2 != k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f329,plain,
    ( ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f327,f77])).

fof(f327,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f326,f37])).

fof(f326,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f325,f252])).

fof(f252,plain,
    ( ! [X0] : r2_hidden(sK2,X0)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f251,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f251,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f244,f79])).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X2)
      | r2_hidden(X1,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f244,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f241,f230])).

fof(f230,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f128,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f39,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f241,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f231,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f58,f54])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f231,plain,
    ( r2_hidden(sK2,k2_relset_1(k1_xboole_0,k1_xboole_0,sK3))
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f129,f140])).

fof(f129,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,k1_xboole_0,sK3))
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f40,f124])).

fof(f325,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(sK3,k1_xboole_0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(sK3,k1_xboole_0))
    | ~ r2_hidden(sK2,k9_relat_1(sK3,k1_xboole_0))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f227,f68])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK3,X0,sK2),k1_xboole_0)
        | ~ r2_hidden(sK2,k9_relat_1(sK3,X0)) )
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f114,f140])).

fof(f224,plain,
    ( ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f214,f166])).

fof(f166,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0))
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f165,f91])).

fof(f91,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f165,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f164,f142])).

fof(f142,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f37,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f164,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0))
    | ~ r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(resolution,[],[f153,f68])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(k1_xboole_0,X0,sK2),sK0)
        | ~ r2_hidden(sK2,k9_relat_1(k1_xboole_0,X0)) )
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f147,f137])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(k1_xboole_0,X0,sK2),sK0)
        | ~ r2_hidden(sK2,k9_relat_1(sK3,X0)) )
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f114,f137])).

fof(f214,plain,
    ( ! [X0] : r2_hidden(sK2,X0)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f213,f42])).

fof(f213,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f211,f79])).

fof(f211,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f206,f150])).

fof(f150,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f128,f137])).

fof(f206,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f82,f151])).

fof(f151,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,k1_xboole_0,k1_xboole_0))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f129,f137])).

fof(f141,plain,
    ( spl7_5
    | spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f134,f123,f139,f136])).

fof(f134,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f130,f127])).

fof(f127,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f38,f124])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f130,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_4 ),
    inference(resolution,[],[f128,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f125,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f118,f123,f120])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f115,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f59,f39])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl7_2 ),
    inference(resolution,[],[f94,f53])).

fof(f94,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_2
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f95,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f88,f93,f90])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f76,f42])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f44,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14188)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (14188)Refutation not found, incomplete strategy% (14188)------------------------------
% 0.21/0.49  % (14188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14188)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14188)Memory used [KB]: 10746
% 0.21/0.49  % (14188)Time elapsed: 0.079 s
% 0.21/0.49  % (14188)------------------------------
% 0.21/0.49  % (14188)------------------------------
% 0.21/0.50  % (14187)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (14196)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (14194)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (14192)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (14204)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (14196)Refutation not found, incomplete strategy% (14196)------------------------------
% 0.21/0.52  % (14196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14196)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14196)Memory used [KB]: 10618
% 0.21/0.52  % (14196)Time elapsed: 0.100 s
% 0.21/0.52  % (14196)------------------------------
% 0.21/0.52  % (14196)------------------------------
% 0.21/0.52  % (14193)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (14200)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (14186)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (14195)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  % (14189)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (14186)Refutation not found, incomplete strategy% (14186)------------------------------
% 0.21/0.53  % (14186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14186)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14186)Memory used [KB]: 10618
% 0.21/0.53  % (14186)Time elapsed: 0.093 s
% 0.21/0.53  % (14186)------------------------------
% 0.21/0.53  % (14186)------------------------------
% 0.21/0.53  % (14187)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f426,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f95,f101,f125,f141,f224,f329,f425])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    ~spl7_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f424])).
% 0.21/0.53  fof(f424,plain,(
% 0.21/0.53    $false | ~spl7_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f423,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    r2_hidden(sK2,k2_relat_1(sK3))),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f39])).
% 0.21/0.53  % (14191)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  % (14190)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    r2_hidden(sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(superposition,[],[f40,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f423,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k2_relat_1(sK3)) | ~spl7_3),
% 0.21/0.53    inference(forward_demodulation,[],[f422,f414])).
% 0.21/0.53  fof(f414,plain,(
% 0.21/0.53    k2_relat_1(sK3) = k9_relat_1(sK3,sK0) | ~spl7_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f404,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    v1_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f75,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.53    inference(resolution,[],[f44,f39])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f404,plain,(
% 0.21/0.53    k2_relat_1(sK3) = k9_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl7_3),
% 0.21/0.53    inference(superposition,[],[f43,f397])).
% 0.21/0.53  fof(f397,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK3) | ~spl7_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f393,f39])).
% 0.21/0.53  fof(f393,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.21/0.53    inference(superposition,[],[f121,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl7_3 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.53  fof(f422,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(sK3,sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f421,f77])).
% 0.21/0.53  fof(f421,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(sK3,sK0)) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f420,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f420,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f419])).
% 0.21/0.53  fof(f419,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(sK3,sK0)) | ~r2_hidden(sK2,k9_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.21/0.53    inference(resolution,[],[f114,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (r2_hidden(sK6(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(sK6(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK4(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X1,X6)) = X6 & r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK4(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK4(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK4(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK4(X0,X1,X2) = k1_funct_1(X0,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X1,X6)) = X6 & r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(rectify,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK6(sK3,X0,sK2),sK0) | ~r2_hidden(sK2,k9_relat_1(sK3,X0))) )),
% 0.21/0.53    inference(equality_resolution,[],[f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK2 != X1 | ~r2_hidden(sK6(sK3,X0,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f107,f77])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK2 != X1 | ~r2_hidden(sK6(sK3,X0,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f106,f37])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sK2 != X1 | ~r2_hidden(sK6(sK3,X0,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.21/0.53    inference(superposition,[],[f41,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK6(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK6(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    ~spl7_4 | ~spl7_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f328])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    $false | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f327,f77])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f326,f37])).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f325,f252])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2,X0)) ) | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f251,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(resolution,[],[f244,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X2,X3,X1] : (~r2_hidden(X1,X2) | r2_hidden(X1,X3) | ~r1_tarski(X2,X3)) )),
% 0.21/0.53    inference(resolution,[],[f54,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.53    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_xboole_0) | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f241,f230])).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(backward_demodulation,[],[f128,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | ~spl7_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f139])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    spl7_6 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_4),
% 0.21/0.53    inference(backward_demodulation,[],[f39,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | ~spl7_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f123])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl7_4 <=> k1_xboole_0 = sK1),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | r2_hidden(sK2,k1_xboole_0) | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(resolution,[],[f231,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k2_relset_1(X1,X2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_hidden(X3,X2)) )),
% 0.21/0.53    inference(resolution,[],[f58,f54])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    r2_hidden(sK2,k2_relset_1(k1_xboole_0,k1_xboole_0,sK3)) | (~spl7_4 | ~spl7_6)),
% 0.21/0.53    inference(backward_demodulation,[],[f129,f140])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    r2_hidden(sK2,k2_relset_1(sK0,k1_xboole_0,sK3)) | ~spl7_4),
% 0.21/0.53    inference(backward_demodulation,[],[f40,f124])).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(sK3,k1_xboole_0)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f324])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(sK3,k1_xboole_0)) | ~r2_hidden(sK2,k9_relat_1(sK3,k1_xboole_0)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl7_6),
% 0.21/0.53    inference(resolution,[],[f227,f68])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK6(sK3,X0,sK2),k1_xboole_0) | ~r2_hidden(sK2,k9_relat_1(sK3,X0))) ) | ~spl7_6),
% 0.21/0.53    inference(backward_demodulation,[],[f114,f140])).
% 0.21/0.53  fof(f224,plain,(
% 0.21/0.53    ~spl7_1 | ~spl7_4 | ~spl7_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f221])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    $false | (~spl7_1 | ~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(resolution,[],[f214,f166])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0)) | (~spl7_1 | ~spl7_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f165,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    v1_relat_1(k1_xboole_0) | ~spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl7_1 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(k1_xboole_0) | ~spl7_5),
% 0.21/0.53    inference(subsumption_resolution,[],[f164,f142])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    v1_funct_1(k1_xboole_0) | ~spl7_5),
% 0.21/0.53    inference(backward_demodulation,[],[f37,f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    k1_xboole_0 = sK3 | ~spl7_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl7_5 <=> k1_xboole_0 = sK3),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl7_5),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f163])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ~r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0)) | ~r2_hidden(sK2,k9_relat_1(k1_xboole_0,sK0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl7_5),
% 0.21/0.53    inference(resolution,[],[f153,f68])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK6(k1_xboole_0,X0,sK2),sK0) | ~r2_hidden(sK2,k9_relat_1(k1_xboole_0,X0))) ) | ~spl7_5),
% 0.21/0.53    inference(forward_demodulation,[],[f147,f137])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK6(k1_xboole_0,X0,sK2),sK0) | ~r2_hidden(sK2,k9_relat_1(sK3,X0))) ) | ~spl7_5),
% 0.21/0.53    inference(backward_demodulation,[],[f114,f137])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2,X0)) ) | (~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f213,f42])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | (~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(resolution,[],[f211,f79])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    r2_hidden(sK2,k1_xboole_0) | (~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f206,f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(backward_demodulation,[],[f128,f137])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | r2_hidden(sK2,k1_xboole_0) | (~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(resolution,[],[f82,f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    r2_hidden(sK2,k2_relset_1(sK0,k1_xboole_0,k1_xboole_0)) | (~spl7_4 | ~spl7_5)),
% 0.21/0.53    inference(backward_demodulation,[],[f129,f137])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    spl7_5 | spl7_6 | ~spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f134,f123,f139,f136])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl7_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_4),
% 0.21/0.53    inference(backward_demodulation,[],[f38,f124])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl7_4),
% 0.21/0.53    inference(resolution,[],[f128,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.21/0.53    inference(equality_resolution,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl7_3 | spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f118,f123,f120])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f115,f38])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.53    inference(resolution,[],[f59,f39])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~spl7_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    $false | ~spl7_2),
% 0.21/0.53    inference(resolution,[],[f94,f53])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl7_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl7_2 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl7_1 | spl7_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f88,f93,f90])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f76,f42])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f44,f55])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (14187)------------------------------
% 0.21/0.53  % (14187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14187)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (14187)Memory used [KB]: 10874
% 0.21/0.53  % (14187)Time elapsed: 0.099 s
% 0.21/0.53  % (14187)------------------------------
% 0.21/0.53  % (14187)------------------------------
% 0.21/0.53  % (14185)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (14184)Success in time 0.172 s
%------------------------------------------------------------------------------
