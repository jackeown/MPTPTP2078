%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 143 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  184 ( 657 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f43,f116,f120])).

fof(f120,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f41,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f118,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f117,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & ( r1_tarski(sK1,X2)
          | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & ( r1_tarski(sK1,sK2)
        | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f117,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f36,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f69,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f69,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(k3_subset_1(sK0,X2),sK1)
      | r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f68,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f68,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(k3_subset_1(sK0,X2),sK1)
      | ~ m1_subset_1(k3_subset_1(sK0,X2),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f67,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(k3_subset_1(sK0,X2),sK1)
      | ~ m1_subset_1(k3_subset_1(sK0,X2),k1_zfmisc_1(sK0))
      | r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f47,plain,(
    ! [X1] :
      ( r1_tarski(X1,k3_subset_1(sK0,sK1))
      | ~ r1_xboole_0(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_xboole_0(X1,X2)
      | r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f36,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f114,f49])).

fof(f49,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f24,f33])).

fof(f114,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f112,f53])).

fof(f53,plain,
    ( ~ r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | spl3_1 ),
    inference(resolution,[],[f37,f32])).

fof(f37,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f112,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f110,f48])).

fof(f48,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
      | r1_xboole_0(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f110,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f109,f23])).

fof(f109,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f39,f35])).

fof(f25,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f39,f35])).

fof(f26,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:05:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (19674)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.45  % (19674)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f121,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f42,f43,f116,f120])).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    ~spl3_1 | spl3_2),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    $false | (~spl3_1 | spl3_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f118,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ~r1_tarski(sK1,sK2) | spl3_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.20/0.45    inference(subsumption_resolution,[],[f117,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(flattening,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2) | ~spl3_1),
% 0.20/0.45    inference(resolution,[],[f36,f94])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_xboole_0(sK1,k3_subset_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK1,X0)) )),
% 0.20/0.45    inference(resolution,[],[f69,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X2] : (~r1_xboole_0(k3_subset_1(sK0,X2),sK1) | r1_tarski(sK1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f68,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X2] : (~r1_xboole_0(k3_subset_1(sK0,X2),sK1) | ~m1_subset_1(k3_subset_1(sK0,X2),k1_zfmisc_1(sK0)) | r1_tarski(sK1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f67,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X2] : (~r1_xboole_0(k3_subset_1(sK0,X2),sK1) | ~m1_subset_1(k3_subset_1(sK0,X2),k1_zfmisc_1(sK0)) | r1_tarski(sK1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f47,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X1] : (r1_tarski(X1,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f23,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_xboole_0(X1,X2) | r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    spl3_1 <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f116,plain,(
% 0.20/0.45    spl3_1 | ~spl3_2),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f115])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f114,f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(resolution,[],[f24,f33])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | (spl3_1 | ~spl3_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f112,f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ~r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | spl3_1),
% 0.20/0.45    inference(resolution,[],[f37,f32])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f35])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    r1_xboole_0(k3_subset_1(sK0,sK2),sK1) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.20/0.45    inference(resolution,[],[f110,f48])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) | r1_xboole_0(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f23,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl3_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f109,f23])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.20/0.45    inference(resolution,[],[f50,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f39])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f24,f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    spl3_1 | spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f25,f39,f35])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ~spl3_1 | ~spl3_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f26,f39,f35])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (19674)------------------------------
% 0.20/0.45  % (19674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (19674)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (19674)Memory used [KB]: 10618
% 0.20/0.45  % (19674)Time elapsed: 0.069 s
% 0.20/0.45  % (19674)------------------------------
% 0.20/0.45  % (19674)------------------------------
% 0.20/0.45  % (19666)Success in time 0.103 s
%------------------------------------------------------------------------------
