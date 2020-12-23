%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  95 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 ( 644 expanded)
%              Number of equality atoms :   60 ( 291 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(subsumption_resolution,[],[f79,f36])).

fof(f36,plain,(
    r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f34,f15])).

fof(f15,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK1 != sK2
    & k2_mcart_1(sK1) = k2_mcart_1(sK2)
    & k1_mcart_1(sK1) = k1_mcart_1(sK2)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0)
    & v1_relat_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_mcart_1(X2) = k2_mcart_1(X1)
                & k1_mcart_1(X2) = k1_mcart_1(X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,X0) )
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,sK0) )
      & v1_relat_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k2_mcart_1(X2) = k2_mcart_1(X1)
            & k1_mcart_1(X2) = k1_mcart_1(X1)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,sK0) )
   => ( ? [X2] :
          ( sK1 != X2
          & k2_mcart_1(X2) = k2_mcart_1(sK1)
          & k1_mcart_1(X2) = k1_mcart_1(sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k2_mcart_1(X2) = k2_mcart_1(sK1)
        & k1_mcart_1(X2) = k1_mcart_1(sK1)
        & m1_subset_1(X2,sK0) )
   => ( sK1 != sK2
      & k2_mcart_1(sK1) = k2_mcart_1(sK2)
      & k1_mcart_1(sK1) = k1_mcart_1(sK2)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ( k2_mcart_1(X2) = k2_mcart_1(X1)
                    & k1_mcart_1(X2) = k1_mcart_1(X1) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ( k2_mcart_1(X2) = k2_mcart_1(X1)
                  & k1_mcart_1(X2) = k1_mcart_1(X1) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_mcart_1)).

fof(f34,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f18,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f78,f19])).

fof(f19,plain,(
    k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,
    ( k1_mcart_1(sK1) != k1_mcart_1(sK2)
    | ~ r2_hidden(sK2,sK0) ),
    inference(subsumption_resolution,[],[f77,f21])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,
    ( sK1 = sK2
    | k1_mcart_1(sK1) != k1_mcart_1(sK2)
    | ~ r2_hidden(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k2_mcart_1(sK1) != k2_mcart_1(sK1)
    | sK1 = sK2
    | k1_mcart_1(sK1) != k1_mcart_1(sK2)
    | ~ r2_hidden(sK2,sK0) ),
    inference(superposition,[],[f40,f20])).

fof(f20,plain,(
    k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0] :
      ( k2_mcart_1(X0) != k2_mcart_1(sK1)
      | sK1 = X0
      | k1_mcart_1(X0) != k1_mcart_1(sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f37,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( sK1 = X0
      | k2_mcart_1(X0) != k2_mcart_1(sK1)
      | k1_mcart_1(X0) != k1_mcart_1(sK1)
      | ~ r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f33,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | k2_mcart_1(X2) != k2_mcart_1(X0)
      | k1_mcart_1(X2) != k1_mcart_1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X2) != k2_mcart_1(X0)
          | k1_mcart_1(X2) != k1_mcart_1(X0)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X2) != k2_mcart_1(X0)
          | k1_mcart_1(X2) != k1_mcart_1(X0)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X2) = k2_mcart_1(X0)
            & k1_mcart_1(X2) = k1_mcart_1(X0)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).

fof(f33,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f31,f15])).

fof(f31,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f17,f22])).

fof(f17,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (24291)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.47  % (24299)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.47  % (24299)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f79,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    r2_hidden(sK2,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f34,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ((sK1 != sK2 & k2_mcart_1(sK1) = k2_mcart_1(sK2) & k1_mcart_1(sK1) = k1_mcart_1(sK2) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)) & v1_relat_1(sK0) & ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & v1_relat_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,sK0)) & v1_relat_1(sK0) & ~v1_xboole_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,sK0)) => (? [X2] : (sK1 != X2 & k2_mcart_1(X2) = k2_mcart_1(sK1) & k1_mcart_1(X2) = k1_mcart_1(sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X2] : (sK1 != X2 & k2_mcart_1(X2) = k2_mcart_1(sK1) & k1_mcart_1(X2) = k1_mcart_1(sK1) & m1_subset_1(X2,sK0)) => (sK1 != sK2 & k2_mcart_1(sK1) = k2_mcart_1(sK2) & k1_mcart_1(sK1) = k1_mcart_1(sK2) & m1_subset_1(sK2,sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & v1_relat_1(X0) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1))) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & (v1_relat_1(X0) & ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ((k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1)) => X1 = X2))))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ((k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1)) => X1 = X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_mcart_1)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f18,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    m1_subset_1(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ~r2_hidden(sK2,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f78,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    k1_mcart_1(sK1) = k1_mcart_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    k1_mcart_1(sK1) != k1_mcart_1(sK2) | ~r2_hidden(sK2,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f77,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    sK1 != sK2),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    sK1 = sK2 | k1_mcart_1(sK1) != k1_mcart_1(sK2) | ~r2_hidden(sK2,sK0)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    k2_mcart_1(sK1) != k2_mcart_1(sK1) | sK1 = sK2 | k1_mcart_1(sK1) != k1_mcart_1(sK2) | ~r2_hidden(sK2,sK0)),
% 0.21/0.47    inference(superposition,[],[f40,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    k2_mcart_1(sK1) = k2_mcart_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (k2_mcart_1(X0) != k2_mcart_1(sK1) | sK1 = X0 | k1_mcart_1(X0) != k1_mcart_1(sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f37,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (sK1 = X0 | k2_mcart_1(X0) != k2_mcart_1(sK1) | k1_mcart_1(X0) != k1_mcart_1(sK1) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.47    inference(resolution,[],[f33,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (X0 = X2 | k2_mcart_1(X2) != k2_mcart_1(X0) | k1_mcart_1(X2) != k1_mcart_1(X0) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (X0 = X2 | k2_mcart_1(X2) != k2_mcart_1(X0) | k1_mcart_1(X2) != k1_mcart_1(X0) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (X0 = X2 | (k2_mcart_1(X2) != k2_mcart_1(X0) | k1_mcart_1(X2) != k1_mcart_1(X0) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((k2_mcart_1(X2) = k2_mcart_1(X0) & k1_mcart_1(X2) = k1_mcart_1(X0) & r2_hidden(X0,X1) & r2_hidden(X2,X1)) => X0 = X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    r2_hidden(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f31,f15])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f17,f22])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    m1_subset_1(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24299)------------------------------
% 0.21/0.47  % (24299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24299)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24299)Memory used [KB]: 1663
% 0.21/0.47  % (24299)Time elapsed: 0.056 s
% 0.21/0.47  % (24299)------------------------------
% 0.21/0.47  % (24299)------------------------------
% 0.21/0.48  % (24280)Success in time 0.117 s
%------------------------------------------------------------------------------
