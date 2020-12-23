%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 465 expanded)
%              Number of leaves         :    7 ( 150 expanded)
%              Depth                    :   28
%              Number of atoms          :  246 (3328 expanded)
%              Number of equality atoms :   83 ( 999 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f80,f30])).

fof(f30,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK4 != sK5
    & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK4,sK2)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f6,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
          & r2_hidden(X3,sK2)
          & r2_hidden(X2,sK2) )
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
        & r2_hidden(X3,sK2)
        & r2_hidden(X2,sK2) )
   => ( sK4 != sK5
      & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
      & r2_hidden(sK5,sK2)
      & r2_hidden(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f80,plain,(
    sK4 = sK5 ),
    inference(subsumption_resolution,[],[f79,f63])).

fof(f63,plain,(
    r2_hidden(sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f28,f59])).

fof(f59,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f58,f30])).

fof(f58,plain,
    ( sK4 = sK5
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f57,f28])).

fof(f57,plain,
    ( ~ r2_hidden(sK5,sK2)
    | sK4 = sK5
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4)
    | ~ r2_hidden(sK5,sK2)
    | sK4 = sK5
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f50,f29])).

fof(f29,plain,(
    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,sK2)
      | sK4 = X0
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f49,f27])).

fof(f27,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK2)
      | ~ r2_hidden(X5,sK2)
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | X4 = X5
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,
    ( sP0(sK3,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f46,f26])).

fof(f26,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,
    ( k1_xboole_0 = sK2
    | ~ v2_funct_1(sK3)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_funct_1(X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_funct_1(X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X2] :
      ( ( ( v2_funct_1(X2)
          | ~ sP0(X2,X0) )
        & ( sP0(X2,X0)
          | ~ v2_funct_1(X2) ) )
      | ~ sP1(X0,X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X2] :
      ( ( v2_funct_1(X2)
      <=> sP0(X2,X0) )
      | ~ sP1(X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f44,plain,
    ( sP1(sK2,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f43,f24])).

fof(f24,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,sK2,sK2)
    | sP1(sK2,sK3) ),
    inference(resolution,[],[f42,f25])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK3,X1,X0)
      | sP1(X1,sK3) ) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | sP1(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

% (27976)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f13,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f8,f12,f11])).

fof(f11,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ! [X3,X4] :
          ( X3 = X4
          | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
          | ~ r2_hidden(X4,X0)
          | ~ r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f33,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | X4 = X5 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK6(X0,X1) != sK7(X0,X1)
          & k1_funct_1(X0,sK6(X0,X1)) = k1_funct_1(X0,sK7(X0,X1))
          & r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X0,X2) = k1_funct_1(X0,X3)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK6(X0,X1) != sK7(X0,X1)
        & k1_funct_1(X0,sK6(X0,X1)) = k1_funct_1(X0,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X0,X2) = k1_funct_1(X0,X3)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ? [X3,X4] :
            ( X3 != X4
            & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            & r2_hidden(X4,X0)
            & r2_hidden(X3,X0) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f28,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,
    ( ~ r2_hidden(sK5,k1_xboole_0)
    | sK4 = sK5 ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4)
    | ~ r2_hidden(sK5,k1_xboole_0)
    | sK4 = sK5 ),
    inference(superposition,[],[f72,f29])).

fof(f72,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | sK4 = X0 ) ),
    inference(resolution,[],[f71,f62])).

fof(f62,plain,(
    r2_hidden(sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f27,f59])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f70,f33])).

fof(f70,plain,(
    sP0(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f69,f26])).

fof(f69,plain,
    ( ~ v2_funct_1(sK3)
    | sP0(sK3,k1_xboole_0) ),
    inference(resolution,[],[f67,f31])).

fof(f67,plain,(
    sP1(k1_xboole_0,sK3) ),
    inference(subsumption_resolution,[],[f66,f23])).

fof(f66,plain,
    ( sP1(k1_xboole_0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f65,f60])).

fof(f60,plain,(
    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f24,f59])).

fof(f65,plain,
    ( sP1(k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f61,f41])).

fof(f41,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | sP1(k1_xboole_0,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f25,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (27955)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (27959)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (27974)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (27971)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (27966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (27975)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (27968)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (27955)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f80,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    sK4 != sK5),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    (sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f6,f15,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) => (sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f6,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.51    inference(flattening,[],[f5])).
% 0.20/0.51  fof(f5,plain,(
% 0.20/0.51    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.51    inference(negated_conjecture,[],[f3])).
% 0.20/0.51  fof(f3,conjecture,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    sK4 = sK5),
% 0.20/0.51    inference(subsumption_resolution,[],[f79,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    r2_hidden(sK5,k1_xboole_0)),
% 0.20/0.51    inference(backward_demodulation,[],[f28,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    k1_xboole_0 = sK2),
% 0.20/0.51    inference(subsumption_resolution,[],[f58,f30])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    sK4 = sK5 | k1_xboole_0 = sK2),
% 0.20/0.51    inference(subsumption_resolution,[],[f57,f28])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ~r2_hidden(sK5,sK2) | sK4 = sK5 | k1_xboole_0 = sK2),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4) | ~r2_hidden(sK5,sK2) | sK4 = sK5 | k1_xboole_0 = sK2),
% 0.20/0.51    inference(superposition,[],[f50,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0] : (k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK2) | sK4 = X0 | k1_xboole_0 = sK2) )),
% 0.20/0.51    inference(resolution,[],[f49,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    r2_hidden(sK4,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X4,X5] : (~r2_hidden(X4,sK2) | ~r2_hidden(X5,sK2) | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | X4 = X5 | k1_xboole_0 = sK2) )),
% 0.20/0.51    inference(resolution,[],[f33,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    sP0(sK3,sK2) | k1_xboole_0 = sK2),
% 0.20/0.51    inference(subsumption_resolution,[],[f46,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    v2_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~v2_funct_1(sK3) | sP0(sK3,sK2)),
% 0.20/0.51    inference(resolution,[],[f44,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_funct_1(X1) | sP0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (((v2_funct_1(X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_funct_1(X1))) | ~sP1(X0,X1))),
% 0.20/0.51    inference(rectify,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X2] : (((v2_funct_1(X2) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~v2_funct_1(X2))) | ~sP1(X0,X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X2] : ((v2_funct_1(X2) <=> sP0(X2,X0)) | ~sP1(X0,X2))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    sP1(sK2,sK3) | k1_xboole_0 = sK2),
% 0.20/0.51    inference(subsumption_resolution,[],[f43,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK2,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK2,sK2) | sP1(sK2,sK3)),
% 0.20/0.51    inference(resolution,[],[f42,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0) | sP1(X1,sK3)) )),
% 0.20/0.51    inference(resolution,[],[f38,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    v1_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | sP1(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  % (27976)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (sP1(X0,X2) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(definition_folding,[],[f8,f12,f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X2,X0] : (sP0(X2,X0) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f7])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | X4 = X5) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : ((sP0(X0,X1) | (sK6(X0,X1) != sK7(X0,X1) & k1_funct_1(X0,sK6(X0,X1)) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK6(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f20,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK6(X0,X1) != sK7(X0,X1) & k1_funct_1(X0,sK6(X0,X1)) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK6(X0,X1),X1)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X2,X0] : ((sP0(X2,X0) | ? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~sP0(X2,X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f11])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    r2_hidden(sK5,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ~r2_hidden(sK5,k1_xboole_0) | sK4 = sK5),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    k1_funct_1(sK3,sK4) != k1_funct_1(sK3,sK4) | ~r2_hidden(sK5,k1_xboole_0) | sK4 = sK5),
% 0.20/0.51    inference(superposition,[],[f72,f29])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X0] : (k1_funct_1(sK3,sK4) != k1_funct_1(sK3,X0) | ~r2_hidden(X0,k1_xboole_0) | sK4 = X0) )),
% 0.20/0.51    inference(resolution,[],[f71,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    r2_hidden(sK4,k1_xboole_0)),
% 0.20/0.51    inference(backward_demodulation,[],[f27,f59])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK3,X0) != k1_funct_1(sK3,X1) | X0 = X1) )),
% 0.20/0.51    inference(resolution,[],[f70,f33])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    sP0(sK3,k1_xboole_0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f69,f26])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ~v2_funct_1(sK3) | sP0(sK3,k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f67,f31])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    sP1(k1_xboole_0,sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f66,f23])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    sP1(k1_xboole_0,sK3) | ~v1_funct_1(sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f65,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.20/0.51    inference(backward_demodulation,[],[f24,f59])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    sP1(k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK3)),
% 0.20/0.51    inference(resolution,[],[f61,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | sP1(k1_xboole_0,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(equality_resolution,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP1(X0,X2) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.51    inference(backward_demodulation,[],[f25,f59])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (27955)------------------------------
% 0.20/0.51  % (27955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27955)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (27955)Memory used [KB]: 6140
% 0.20/0.51  % (27955)Time elapsed: 0.106 s
% 0.20/0.51  % (27955)------------------------------
% 0.20/0.51  % (27955)------------------------------
% 0.20/0.51  % (27956)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (27953)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (27969)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (27951)Success in time 0.156 s
%------------------------------------------------------------------------------
