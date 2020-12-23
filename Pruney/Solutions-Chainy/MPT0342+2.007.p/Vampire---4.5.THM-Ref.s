%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 332 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f78])).

fof(f78,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f74,f53])).

fof(f53,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_4
  <=> r2_hidden(sK3(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK1)
    | spl4_3 ),
    inference(resolution,[],[f71,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK1,sK2)
    & ! [X3] :
        ( r2_hidden(X3,sK2)
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & ! [X3] :
                ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,sK1)
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,X2)
        & ! [X3] :
            ( r2_hidden(X3,X2)
            | ~ r2_hidden(X3,sK1)
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,sK2)
      & ! [X3] :
          ( r2_hidden(X3,sK2)
          | ~ r2_hidden(X3,sK1)
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                   => r2_hidden(X3,X2) ) )
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f71,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK3(sK1,sK2),X1) )
    | spl4_3 ),
    inference(resolution,[],[f28,f50])).

fof(f50,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_3
  <=> r2_hidden(sK3(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f57,f23])).

fof(f23,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,
    ( r1_tarski(sK1,sK2)
    | spl4_4 ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f54,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f55,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f35,f52,f48])).

fof(f35,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK1)
    | ~ r2_hidden(sK3(sK1,sK2),sK0) ),
    inference(resolution,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f34,plain,(
    ~ r2_hidden(sK3(sK1,sK2),sK2) ),
    inference(resolution,[],[f30,f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (26797)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % (26811)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (26797)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f55,f60,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl4_3 | ~spl4_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    $false | (spl4_3 | ~spl4_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    r2_hidden(sK3(sK1,sK2),sK1) | ~spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl4_4 <=> r2_hidden(sK3(sK1,sK2),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK1,sK2),sK1) | spl4_3),
% 0.21/0.47    inference(resolution,[],[f71,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    (~r1_tarski(sK1,sK2) & ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(sK1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X2] : (~r1_tarski(sK1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,sK2) & ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & ! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK1,sK2),X1)) ) | spl4_3),
% 0.21/0.47    inference(resolution,[],[f28,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK1,sK2),sK0) | spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl4_3 <=> r2_hidden(sK3(sK1,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl4_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    $false | spl4_4),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ~r1_tarski(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    r1_tarski(sK1,sK2) | spl4_4),
% 0.21/0.47    inference(resolution,[],[f54,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK1,sK2),sK1) | spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~spl4_3 | ~spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f52,f48])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK1,sK2),sK1) | ~r2_hidden(sK3(sK1,sK2),sK0)),
% 0.21/0.47    inference(resolution,[],[f34,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.47    inference(resolution,[],[f32,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f25,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK1,sK2),sK2)),
% 0.21/0.47    inference(resolution,[],[f30,f23])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (26797)------------------------------
% 0.21/0.47  % (26797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (26797)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (26797)Memory used [KB]: 5373
% 0.21/0.47  % (26797)Time elapsed: 0.063 s
% 0.21/0.47  % (26797)------------------------------
% 0.21/0.47  % (26797)------------------------------
% 0.21/0.47  % (26795)Success in time 0.119 s
%------------------------------------------------------------------------------
