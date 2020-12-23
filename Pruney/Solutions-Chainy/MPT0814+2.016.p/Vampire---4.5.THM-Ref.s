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
% DateTime   : Thu Dec  3 12:56:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  74 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 202 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f28,f36,f54,f72,f95,f115])).

fof(f115,plain,
    ( ~ spl6_3
    | ~ spl6_5
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_5
    | spl6_7 ),
    inference(subsumption_resolution,[],[f113,f67])).

fof(f67,plain,
    ( ~ r2_hidden(sK5(sK0),sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_7
  <=> r2_hidden(sK5(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f113,plain,
    ( r2_hidden(sK5(sK0),sK2)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f57,f35])).

fof(f35,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl6_3
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f57,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3))
        | r2_hidden(sK5(sK0),X3) )
    | ~ spl6_5 ),
    inference(superposition,[],[f16,f53])).

fof(f53,plain,
    ( sK0 = k4_tarski(sK4(sK0),sK5(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_5
  <=> sK0 = k4_tarski(sK4(sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f95,plain,
    ( ~ spl6_3
    | ~ spl6_5
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_5
    | spl6_8 ),
    inference(subsumption_resolution,[],[f93,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK4(sK0),sK1)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_8
  <=> r2_hidden(sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f93,plain,
    ( r2_hidden(sK4(sK0),sK1)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | r2_hidden(sK4(sK0),X0) )
    | ~ spl6_5 ),
    inference(superposition,[],[f15,f53])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f58,f51,f69,f65])).

fof(f58,plain,
    ( ~ r2_hidden(sK4(sK0),sK1)
    | ~ r2_hidden(sK5(sK0),sK2)
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK4(sK0),sK1)
    | ~ r2_hidden(sK5(sK0),sK2)
    | ~ spl6_5 ),
    inference(superposition,[],[f10,f53])).

fof(f10,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X4,sK1)
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f54,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f37,f33,f51])).

fof(f37,plain,
    ( sK0 = k4_tarski(sK4(sK0),sK5(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f35,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f36,plain,
    ( spl6_3
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f30,f25,f19,f33])).

fof(f19,plain,
    ( spl6_1
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f25,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f30,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f29,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f27,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f28,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f11,f25])).

fof(f11,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f12,f19])).

fof(f12,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (31512)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (31505)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (31511)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (31516)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (31505)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f22,f28,f36,f54,f72,f95,f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~spl6_3 | ~spl6_5 | spl6_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    $false | (~spl6_3 | ~spl6_5 | spl6_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f113,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK0),sK2) | spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl6_7 <=> r2_hidden(sK5(sK0),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    r2_hidden(sK5(sK0),sK2) | (~spl6_3 | ~spl6_5)),
% 0.21/0.49    inference(resolution,[],[f57,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl6_3 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | r2_hidden(sK5(sK0),X3)) ) | ~spl6_5),
% 0.21/0.49    inference(superposition,[],[f16,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl6_5 <=> sK0 = k4_tarski(sK4(sK0),sK5(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~spl6_3 | ~spl6_5 | spl6_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    $false | (~spl6_3 | ~spl6_5 | spl6_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0),sK1) | spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl6_8 <=> r2_hidden(sK4(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    r2_hidden(sK4(sK0),sK1) | (~spl6_3 | ~spl6_5)),
% 0.21/0.49    inference(resolution,[],[f56,f35])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(sK4(sK0),X0)) ) | ~spl6_5),
% 0.21/0.49    inference(superposition,[],[f15,f53])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~spl6_7 | ~spl6_8 | ~spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f51,f69,f65])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0),sK1) | ~r2_hidden(sK5(sK0),sK2) | ~spl6_5),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    sK0 != sK0 | ~r2_hidden(sK4(sK0),sK1) | ~r2_hidden(sK5(sK0),sK2) | ~spl6_5),
% 0.21/0.49    inference(superposition,[],[f10,f53])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK0 | ~r2_hidden(X4,sK1) | ~r2_hidden(X5,sK2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl6_5 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f33,f51])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f35,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK4(X0),sK5(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    spl6_3 | ~spl6_1 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f25,f19,f33])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    spl6_1 <=> r2_hidden(sK0,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    spl6_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(resolution,[],[f29,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    r2_hidden(sK0,sK3) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f19])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,k2_zfmisc_1(sK1,sK2))) ) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f27,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f25])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f11,f25])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f12,f19])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    r2_hidden(sK0,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (31505)------------------------------
% 0.21/0.49  % (31505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31505)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (31505)Memory used [KB]: 10618
% 0.21/0.49  % (31505)Time elapsed: 0.084 s
% 0.21/0.49  % (31505)------------------------------
% 0.21/0.49  % (31505)------------------------------
% 0.21/0.49  % (31501)Success in time 0.134 s
%------------------------------------------------------------------------------
