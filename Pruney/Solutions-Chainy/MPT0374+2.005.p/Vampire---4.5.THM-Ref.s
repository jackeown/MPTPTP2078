%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 133 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  249 ( 495 expanded)
%              Number of equality atoms :   41 (  91 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f131,f141,f145,f316])).

fof(f316,plain,
    ( ~ spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl5_2
    | spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f314,f123])).

fof(f123,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f314,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f312,f50])).

fof(f50,plain,(
    ~ m1_subset_1(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X2,sK0) )
   => ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

fof(f312,plain,
    ( m1_subset_1(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f290,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f290,plain,
    ( r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f284,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f284,plain,
    ( r1_tarski(k1_enumset1(sK1,sK1,sK2),sK0)
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_enumset1(sK1,sK1,sK2),sK0)
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(superposition,[],[f45,f270])).

fof(f270,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_enumset1(sK1,sK1,sK2),sK0)
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f261,f65])).

fof(f65,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X0,sK2),sK0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f140,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f49,f36])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f140,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_7
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f145,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f143,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f61,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f141,plain,
    ( spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f72,f138,f59])).

fof(f72,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f131,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f124,f120])).

fof(f120,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f108,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
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

fof(f108,plain,
    ( r2_hidden(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f104,f54])).

fof(f104,plain,
    ( r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0)
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0)
    | ~ spl5_2 ),
    inference(superposition,[],[f45,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_enumset1(sK1,sK1,sK1),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f77,f65])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X0,sK1),sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f65,f51])).

fof(f124,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f66,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f56,f63,f59])).

fof(f56,plain,
    ( r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f29,f37])).

fof(f29,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:34:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (1299)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (1299)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (1291)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f66,f131,f141,f145,f316])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    ~spl5_2 | spl5_4 | ~spl5_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f315])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    $false | (~spl5_2 | spl5_4 | ~spl5_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f314,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_zfmisc_1(sK0)) | spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl5_4 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    v1_xboole_0(k1_zfmisc_1(sK0)) | (~spl5_2 | ~spl5_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f312,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ~m1_subset_1(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(definition_unfolding,[],[f32,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X2] : (~m1_subset_1(k2_tarski(sK1,X2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(X2,sK0)) => (~m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(sK0)) & k1_xboole_0 != sK0 & m1_subset_1(sK2,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    m1_subset_1(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | (~spl5_2 | ~spl5_7)),
% 0.21/0.49    inference(resolution,[],[f290,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    r2_hidden(k1_enumset1(sK1,sK1,sK2),k1_zfmisc_1(sK0)) | (~spl5_2 | ~spl5_7)),
% 0.21/0.49    inference(resolution,[],[f284,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X3] : (~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    r1_tarski(k1_enumset1(sK1,sK1,sK2),sK0) | (~spl5_2 | ~spl5_7)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f283])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_enumset1(sK1,sK1,sK2),sK0) | (~spl5_2 | ~spl5_7)),
% 0.21/0.49    inference(superposition,[],[f45,f270])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK1,sK1,sK2),sK0) | (~spl5_2 | ~spl5_7)),
% 0.21/0.49    inference(resolution,[],[f261,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    r2_hidden(sK1,sK0) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl5_2 <=> r2_hidden(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X0,sK2),sK0)) ) | ~spl5_7),
% 0.21/0.49    inference(resolution,[],[f140,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f49,f36])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.49    inference(nnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    r2_hidden(sK2,sK0) | ~spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl5_7 <=> r2_hidden(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~spl5_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    $false | ~spl5_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f143,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f61,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    v1_xboole_0(sK0) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl5_1 <=> v1_xboole_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl5_1 | spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f72,f138,f59])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f30,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ~spl5_2 | ~spl5_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    $false | (~spl5_2 | ~spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f124,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f108,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(rectify,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    r2_hidden(k1_enumset1(sK1,sK1,sK1),k1_zfmisc_1(sK0)) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f104,f54])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0) | ~spl5_2),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_enumset1(sK1,sK1,sK1),sK0) | ~spl5_2),
% 0.21/0.50    inference(superposition,[],[f45,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK1,sK1,sK1),sK0) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f77,f65])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X0,sK1),sK0)) ) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f65,f51])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl5_1 | spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f63,f59])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    r2_hidden(sK1,sK0) | v1_xboole_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f29,f37])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    m1_subset_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1299)------------------------------
% 0.21/0.50  % (1299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1299)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1299)Memory used [KB]: 10746
% 0.21/0.50  % (1299)Time elapsed: 0.071 s
% 0.21/0.50  % (1299)------------------------------
% 0.21/0.50  % (1299)------------------------------
% 0.21/0.50  % (1290)Success in time 0.138 s
%------------------------------------------------------------------------------
