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
% DateTime   : Thu Dec  3 12:46:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  90 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 303 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f79,f108,f120])).

fof(f120,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f14,f45,f52,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f52,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f45,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f14,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f108,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f14,f49])).

fof(f49,plain,
    ( sK1 = sK2
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f79,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f15,f55,f58,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f58,plain,
    ( ~ m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f53,f55,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2)
      | ~ r2_hidden(sK3(X0,sK2),sK1)
      | ~ m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f12,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f12,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f55,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f53,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f36,f51,f47,f43])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f35,f21])).

fof(f35,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,sK1),sK2)
      | ~ r1_tarski(sK1,X1)
      | sK1 = X1 ) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,sK1),sK2)
      | ~ r1_tarski(sK1,X1)
      | sK1 = X1
      | ~ r2_hidden(sK3(X1,sK1),sK2) ) ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f13,f19])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0,sK1),k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(X0,sK1),sK2)
      | ~ r1_tarski(sK1,X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f29,f18])).

fof(f29,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK3(X0,sK1),k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(X0,sK1),sK2) ) ),
    inference(resolution,[],[f11,f22])).

fof(f11,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:38:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (2316)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (2308)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (2296)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (2296)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (2300)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (2313)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (2299)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f54,f79,f108,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~spl4_1 | ~spl4_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    $false | (~spl4_1 | ~spl4_3)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f14,f45,f52,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl4_3 <=> r1_tarski(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    r1_tarski(sK2,sK1) | ~spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    spl4_1 <=> r1_tarski(sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    sK1 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~spl4_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    $false | ~spl4_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f14,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    sK1 = sK2 | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl4_2 <=> sK1 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl4_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    $false | spl4_3),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f15,f55,f58,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~m1_subset_1(sK3(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_3),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f53,f55,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,sK2) | ~r2_hidden(sK3(X0,sK2),sK1) | ~m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(sK0))) )),
% 0.21/0.52    inference(resolution,[],[f12,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK2) | spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    r2_hidden(sK3(sK1,sK2),sK1) | spl4_3),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f53,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl4_1 | spl4_2 | ~spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f51,f47,f43])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK2) | sK1 = sK2 | r1_tarski(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f35,f21])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(sK3(X1,sK1),sK2) | ~r1_tarski(sK1,X1) | sK1 = X1) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(sK3(X1,sK1),sK2) | ~r1_tarski(sK1,X1) | sK1 = X1 | ~r2_hidden(sK3(X1,sK1),sK2)) )),
% 0.21/0.52    inference(resolution,[],[f31,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f13,f19])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK3(X0,sK1),k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(X0,sK1),sK2) | ~r1_tarski(sK1,X0) | sK1 = X0) )),
% 0.21/0.52    inference(resolution,[],[f29,f18])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,sK1) | ~m1_subset_1(sK3(X0,sK1),k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(X0,sK1),sK2)) )),
% 0.21/0.52    inference(resolution,[],[f11,f22])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2296)------------------------------
% 0.21/0.52  % (2296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2296)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2296)Memory used [KB]: 6268
% 0.21/0.52  % (2296)Time elapsed: 0.109 s
% 0.21/0.52  % (2296)------------------------------
% 0.21/0.52  % (2296)------------------------------
% 0.21/0.52  % (2286)Success in time 0.16 s
%------------------------------------------------------------------------------
