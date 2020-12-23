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
% DateTime   : Thu Dec  3 12:46:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 120 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 ( 501 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f101,f108])).

fof(f108,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f106,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v3_setfam_1(sK2,sK0)
    & r1_tarski(sK2,sK1)
    & v3_setfam_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(X2,X0)
            & r1_tarski(X2,X1)
            & v3_setfam_1(X1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(X2,sK0)
          & r1_tarski(X2,sK1)
          & v3_setfam_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v3_setfam_1(X2,sK0)
        & r1_tarski(X2,sK1)
        & v3_setfam_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ v3_setfam_1(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & v3_setfam_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ( r1_tarski(X2,X1)
                & v3_setfam_1(X1,X0) )
             => v3_setfam_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ( r1_tarski(X2,X1)
              & v3_setfam_1(X1,X0) )
           => v3_setfam_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).

fof(f106,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f103,f24])).

fof(f24,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,
    ( ~ v3_setfam_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(resolution,[],[f96,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f96,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f101,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f98,f25])).

fof(f25,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_3 ),
    inference(resolution,[],[f92,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f92,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f97,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f62,f94,f90])).

fof(f62,plain,
    ( r2_hidden(sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f49,f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f37,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f37,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f36,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,
    ( r2_hidden(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f32,f26])).

fof(f26,plain,(
    ~ v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_setfam_1(X1,X0)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK1)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f47,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f47,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f42,f25])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f40,f33])).

fof(f40,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f37,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (8988)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.44  % (8988)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f97,f101,f108])).
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    ~spl3_4),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    $false | ~spl3_4),
% 0.20/0.45    inference(subsumption_resolution,[],[f106,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    (~v3_setfam_1(sK2,sK0) & r1_tarski(sK2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~v3_setfam_1(X2,sK0) & r1_tarski(X2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ? [X2] : (~v3_setfam_1(X2,sK0) & r1_tarski(X2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~v3_setfam_1(sK2,sK0) & r1_tarski(sK2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.45    inference(flattening,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((~v3_setfam_1(X2,X0) & (r1_tarski(X2,X1) & v3_setfam_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.20/0.45    inference(negated_conjecture,[],[f6])).
% 0.20/0.45  fof(f6,conjecture,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).
% 0.20/0.45  fof(f106,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.20/0.45    inference(subsumption_resolution,[],[f103,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    v3_setfam_1(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    ~v3_setfam_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.20/0.45    inference(resolution,[],[f96,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.45    inference(nnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    r2_hidden(sK0,sK1) | ~spl3_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f94])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    spl3_4 <=> r2_hidden(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    spl3_3),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f100])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    $false | spl3_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f98,f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    r1_tarski(sK2,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ~r1_tarski(sK2,sK1) | spl3_3),
% 0.20/0.45    inference(resolution,[],[f92,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.45    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f90])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    ~spl3_3 | spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f62,f94,f90])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    r2_hidden(sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.20/0.45    inference(resolution,[],[f49,f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(resolution,[],[f37,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    r2_hidden(sK0,sK2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f36,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    r2_hidden(sK0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.45    inference(resolution,[],[f32,f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ~v3_setfam_1(sK2,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v3_setfam_1(X1,X0) | r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X1] : (~m1_subset_1(X1,sK1) | r2_hidden(X1,sK1)) )),
% 0.20/0.45    inference(resolution,[],[f47,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | r2_hidden(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ~v1_xboole_0(sK1)),
% 0.20/0.45    inference(resolution,[],[f42,f25])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(sK2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.45    inference(resolution,[],[f40,f33])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) )),
% 0.20/0.45    inference(resolution,[],[f37,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (8988)------------------------------
% 0.20/0.45  % (8988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (8988)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (8988)Memory used [KB]: 5373
% 0.20/0.45  % (8988)Time elapsed: 0.055 s
% 0.20/0.45  % (8988)------------------------------
% 0.20/0.45  % (8988)------------------------------
% 0.20/0.46  % (8987)Success in time 0.108 s
%------------------------------------------------------------------------------
