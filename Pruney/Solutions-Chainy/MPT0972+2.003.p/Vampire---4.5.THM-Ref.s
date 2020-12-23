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
% DateTime   : Thu Dec  3 13:01:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 (1738 expanded)
%              Number of leaves         :   15 ( 531 expanded)
%              Depth                    :   26
%              Number of atoms          :  392 (12593 expanded)
%              Number of equality atoms :  157 (2638 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(global_subsumption,[],[f211,f242])).

fof(f242,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f208,f233])).

fof(f233,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f224,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f51,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f224,plain,(
    v1_xboole_0(sK4) ),
    inference(resolution,[],[f185,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f185,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f175,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f175,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f41,f171])).

fof(f171,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f98,f160])).

fof(f160,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f43,f156])).

% (29987)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f156,plain,
    ( sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f39,f77,f128,f155])).

fof(f155,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,
    ( sK1 != sK1
    | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( sK1 != sK1
    | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f148,f105])).

fof(f105,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f40,f104])).

fof(f104,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f101,f91])).

fof(f91,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f54,f85])).

fof(f85,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f58,f41])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f40,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ r2_hidden(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f27,f26])).

fof(f26,plain,
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
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
              | ~ r2_hidden(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK1,sK2,sK3,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
            | ~ r2_hidden(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
      & ! [X4] :
          ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
          | ~ r2_hidden(X4,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f148,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0))
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK2 ) ),
    inference(global_subsumption,[],[f36,f76,f142])).

fof(f142,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0))
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f47,f103])).

fof(f103,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f37,f102])).

fof(f102,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f100,f90])).

fof(f90,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f54,f84])).

fof(f84,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f58,f38])).

fof(f37,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f76,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f52,f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f128,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))
    | k1_xboole_0 = sK2
    | sK3 = sK4 ),
    inference(global_subsumption,[],[f39,f77,f127])).

fof(f127,plain,
    ( sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( sK1 != sK1
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( sK1 != sK1
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f120,f105])).

fof(f120,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK2
      | k1_funct_1(sK3,sK5(sK3,X0)) = k1_funct_1(sK4,sK5(sK3,X0)) ) ),
    inference(resolution,[],[f114,f42])).

fof(f42,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f114,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,X0),sK1)
      | k1_relat_1(X0) != sK1
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK2 ) ),
    inference(global_subsumption,[],[f36,f76,f108])).

fof(f108,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | r2_hidden(sK5(sK3,X0),sK1)
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f46,f103])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f52,f41])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    r2_relset_1(sK1,sK2,sK3,sK3) ),
    inference(global_subsumption,[],[f80,f94])).

fof(f94,plain,
    ( r2_relset_1(sK1,sK2,sK3,sK3)
    | sP6(sK2,sK1) ),
    inference(resolution,[],[f69,f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f69_D])).

fof(f69_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP6(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f80,plain,(
    ~ sP6(sK2,sK1) ),
    inference(resolution,[],[f70,f38])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP6(X1,X0) ) ),
    inference(general_splitting,[],[f61,f69_D])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f208,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f176,f202])).

fof(f202,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f187,f73])).

fof(f187,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f184,f75])).

fof(f184,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f173,f62])).

fof(f173,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f38,f171])).

fof(f176,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,sK3,sK4) ),
    inference(backward_demodulation,[],[f43,f171])).

fof(f211,plain,(
    r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f182,f202])).

fof(f182,plain,(
    r2_relset_1(sK1,k1_xboole_0,sK3,sK3) ),
    inference(backward_demodulation,[],[f98,f171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (29980)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (29972)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (29979)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (29979)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (29971)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(global_subsumption,[],[f211,f242])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f208,f233])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    k1_xboole_0 = sK4),
% 0.21/0.52    inference(resolution,[],[f224,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f51,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    v1_xboole_0(sK4)),
% 0.21/0.52    inference(resolution,[],[f185,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f45,f44])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    inference(forward_demodulation,[],[f175,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.52    inference(backward_demodulation,[],[f41,f171])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    k1_xboole_0 = sK2),
% 0.21/0.52    inference(global_subsumption,[],[f98,f160])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK2,sK3,sK3) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(superposition,[],[f43,f156])).
% 0.21/0.52  % (29987)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    sK3 = sK4 | k1_xboole_0 = sK2),
% 0.21/0.52    inference(global_subsumption,[],[f39,f77,f128,f155])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    sK1 != sK1 | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    sK1 != sK1 | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.21/0.52    inference(superposition,[],[f148,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(global_subsumption,[],[f40,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    sK1 = k1_relat_1(sK4) | ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(forward_demodulation,[],[f101,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 0.21/0.52    inference(resolution,[],[f53,f41])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.21/0.52    inference(resolution,[],[f54,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    sP0(sK1,sK4,sK2)),
% 0.21/0.52    inference(resolution,[],[f58,f41])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(definition_folding,[],[f21,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f24])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    v1_funct_2(sK4,sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f13,f27,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(X0) != sK1 | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0)) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK2) )),
% 0.21/0.52    inference(global_subsumption,[],[f36,f76,f142])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(X0) != sK1 | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0)) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2) )),
% 0.21/0.52    inference(superposition,[],[f47,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(global_subsumption,[],[f37,f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    sK1 = k1_relat_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(forward_demodulation,[],[f100,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.21/0.52    inference(resolution,[],[f53,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.52    inference(resolution,[],[f54,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    sP0(sK1,sK3,sK2)),
% 0.21/0.52    inference(resolution,[],[f58,f38])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    v1_relat_1(sK3)),
% 0.21/0.52    inference(resolution,[],[f52,f38])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) | k1_xboole_0 = sK2 | sK3 = sK4),
% 0.21/0.52    inference(global_subsumption,[],[f39,f77,f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    sK1 != sK1 | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    sK1 != sK1 | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) | k1_xboole_0 = sK2),
% 0.21/0.52    inference(superposition,[],[f120,f105])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(X0) != sK1 | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK3,X0)) = k1_funct_1(sK4,sK5(sK3,X0))) )),
% 0.21/0.52    inference(resolution,[],[f114,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK1) | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK5(sK3,X0),sK1) | k1_relat_1(X0) != sK1 | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK2) )),
% 0.21/0.52    inference(global_subsumption,[],[f36,f76,f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK5(sK3,X0),sK1) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2) )),
% 0.21/0.52    inference(superposition,[],[f46,f103])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    v1_relat_1(sK4)),
% 0.21/0.52    inference(resolution,[],[f52,f41])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    r2_relset_1(sK1,sK2,sK3,sK3)),
% 0.21/0.52    inference(global_subsumption,[],[f80,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    r2_relset_1(sK1,sK2,sK3,sK3) | sP6(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f69,f38])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP6(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f69_D])).
% 0.21/0.52  fof(f69_D,plain,(
% 0.21/0.52    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP6(X1,X0)) )),
% 0.21/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~sP6(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f70,f38])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP6(X1,X0)) )),
% 0.21/0.52    inference(general_splitting,[],[f61,f69_D])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4)),
% 0.21/0.52    inference(backward_demodulation,[],[f176,f202])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    k1_xboole_0 = sK3),
% 0.21/0.52    inference(resolution,[],[f187,f73])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    v1_xboole_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f184,f75])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    inference(forward_demodulation,[],[f173,f62])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.52    inference(backward_demodulation,[],[f38,f171])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ~r2_relset_1(sK1,k1_xboole_0,sK3,sK4)),
% 0.21/0.52    inference(backward_demodulation,[],[f43,f171])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f182,f202])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    r2_relset_1(sK1,k1_xboole_0,sK3,sK3)),
% 0.21/0.52    inference(backward_demodulation,[],[f98,f171])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (29979)------------------------------
% 0.21/0.52  % (29979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29979)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (29979)Memory used [KB]: 6396
% 0.21/0.52  % (29979)Time elapsed: 0.087 s
% 0.21/0.52  % (29979)------------------------------
% 0.21/0.52  % (29979)------------------------------
% 0.21/0.52  % (29966)Success in time 0.166 s
%------------------------------------------------------------------------------
