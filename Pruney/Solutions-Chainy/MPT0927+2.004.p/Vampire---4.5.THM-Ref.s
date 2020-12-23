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
% DateTime   : Thu Dec  3 12:59:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 561 expanded)
%              Number of leaves         :   35 ( 228 expanded)
%              Depth                    :   12
%              Number of atoms          :  507 (3093 expanded)
%              Number of equality atoms :   97 ( 240 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f147,f189,f208,f219,f223,f242,f261,f262,f279,f280,f304,f323,f330,f336,f337,f338,f339,f348,f351,f354])).

fof(f354,plain,
    ( spl10_4
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl10_4
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f79,f352])).

fof(f352,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | spl10_4
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f69,f111])).

fof(f111,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl10_12
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f69,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl10_4
  <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f79,plain,(
    r2_hidden(k2_mcart_1(sK8),sK7) ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f52,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f34,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
    & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f22,f21,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                        & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                        & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                    & m1_subset_1(X7,k1_zfmisc_1(X3)) )
                & m1_subset_1(X6,k1_zfmisc_1(X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X1)) )
        & m1_subset_1(X4,k1_zfmisc_1(X0)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                      & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                    & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
            & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                  & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                  & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
              & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

% (20121)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (20126)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (20124)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (20135)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (20147)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (20136)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (20143)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (20142)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (20139)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (20137)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (20128)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (20128)Refutation not found, incomplete strategy% (20128)------------------------------
% (20128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20128)Termination reason: Refutation not found, incomplete strategy

% (20128)Memory used [KB]: 10746
% (20128)Time elapsed: 0.148 s
% (20128)------------------------------
% (20128)------------------------------
% (20134)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (20144)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (20131)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (20129)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (20122)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (20129)Refutation not found, incomplete strategy% (20129)------------------------------
% (20129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20129)Termination reason: Refutation not found, incomplete strategy

% (20129)Memory used [KB]: 10746
% (20129)Time elapsed: 0.156 s
% (20129)------------------------------
% (20129)------------------------------
fof(f20,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ? [X8] :
                ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                  | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                  | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                  | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
            & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
        & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
   => ( ? [X7] :
          ( ? [X8] :
              ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
                | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
              & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
              & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
          & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

% (20145)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f21,plain,
    ( ? [X7] :
        ( ? [X8] :
            ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
              | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
              | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
              | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
            & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
            & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
        & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
   => ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
            | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
            | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
            | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
          & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
          & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & m1_subset_1(sK7,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X8] :
        ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
          | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
          | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
          | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
        & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
        & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
      & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
      & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X0))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X1))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X2))
               => ! [X7] :
                    ( m1_subset_1(X7,k1_zfmisc_1(X3))
                   => ! [X8] :
                        ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                       => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                         => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                            & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                            & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                            & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X0))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X1))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X2))
             => ! [X7] :
                  ( m1_subset_1(X7,k1_zfmisc_1(X3))
                 => ! [X8] :
                      ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                     => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                       => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f351,plain,
    ( spl10_3
    | ~ spl10_11 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | spl10_3
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f126,f349])).

fof(f349,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | spl10_3
    | ~ spl10_11 ),
    inference(forward_demodulation,[],[f66,f107])).

fof(f107,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl10_11
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f66,plain,
    ( ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl10_3
  <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f126,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(resolution,[],[f78,f45])).

fof(f78,plain,(
    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f348,plain,
    ( spl10_2
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl10_2
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f167,f346])).

fof(f346,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | spl10_2
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f63,f103])).

fof(f103,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl10_10
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f63,plain,
    ( ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl10_2
  <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f167,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    inference(resolution,[],[f125,f45])).

fof(f125,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f78,f44])).

fof(f339,plain,
    ( spl10_5
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_12 ),
    inference(avatar_split_clause,[],[f335,f110,f95,f92,f89,f86])).

fof(f86,plain,
    ( spl10_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f89,plain,
    ( spl10_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f92,plain,
    ( spl10_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f95,plain,
    ( spl10_8
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f335,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f53,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f53,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f33,f51])).

fof(f33,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f338,plain,
    ( spl10_5
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_11 ),
    inference(avatar_split_clause,[],[f334,f106,f95,f92,f89,f86])).

fof(f334,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f337,plain,
    ( spl10_5
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_10 ),
    inference(avatar_split_clause,[],[f333,f102,f95,f92,f89,f86])).

fof(f333,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f53,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f336,plain,
    ( spl10_5
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9 ),
    inference(avatar_split_clause,[],[f332,f98,f95,f92,f89,f86])).

fof(f98,plain,
    ( spl10_9
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f332,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f330,plain,(
    ~ spl10_20 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f166,f164])).

fof(f164,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl10_20
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f166,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    inference(resolution,[],[f125,f44])).

fof(f323,plain,
    ( ~ spl10_5
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl10_5
    | spl10_21 ),
    inference(subsumption_resolution,[],[f36,f320])).

fof(f320,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_5
    | spl10_21 ),
    inference(backward_demodulation,[],[f218,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f218,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl10_21
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f304,plain,(
    ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f79,f155])).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK7)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl10_18
  <=> ! [X0] : ~ r2_hidden(X0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f280,plain,
    ( ~ spl10_17
    | spl10_18 ),
    inference(avatar_split_clause,[],[f257,f154,f151])).

fof(f151,plain,
    ( spl10_17
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f257,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK7)
      | ~ v1_xboole_0(sK3) ) ),
    inference(resolution,[],[f113,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f113,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK7) ) ),
    inference(resolution,[],[f76,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f76,plain,(
    r1_tarski(sK7,sK3) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f32,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f279,plain,(
    ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl10_14 ),
    inference(resolution,[],[f167,f137])).

fof(f137,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl10_14
  <=> ! [X0] : ~ r2_hidden(X0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f262,plain,
    ( ~ spl10_13
    | spl10_14 ),
    inference(avatar_split_clause,[],[f220,f136,f133])).

fof(f133,plain,
    ( spl10_13
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f220,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK5)
      | ~ v1_xboole_0(sK1) ) ),
    inference(resolution,[],[f75,f37])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK5) ) ),
    inference(resolution,[],[f73,f38])).

fof(f73,plain,(
    r1_tarski(sK5,sK1) ),
    inference(resolution,[],[f30,f41])).

fof(f30,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f261,plain,
    ( spl10_1
    | ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | spl10_1
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f254,f166])).

fof(f254,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | spl10_1
    | ~ spl10_9 ),
    inference(backward_demodulation,[],[f60,f99])).

fof(f99,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f60,plain,
    ( ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl10_1
  <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f242,plain,
    ( ~ spl10_8
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl10_8
    | spl10_17 ),
    inference(subsumption_resolution,[],[f36,f236])).

fof(f236,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_8
    | spl10_17 ),
    inference(backward_demodulation,[],[f152,f96])).

fof(f96,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f152,plain,
    ( ~ v1_xboole_0(sK3)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f223,plain,(
    ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f126,f146])).

fof(f146,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl10_16
  <=> ! [X0] : ~ r2_hidden(X0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f219,plain,
    ( ~ spl10_21
    | spl10_20 ),
    inference(avatar_split_clause,[],[f214,f163,f217])).

fof(f214,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | ~ v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f72,f37])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f71,f38])).

fof(f71,plain,(
    r1_tarski(sK4,sK0) ),
    inference(resolution,[],[f29,f41])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f208,plain,
    ( ~ spl10_7
    | spl10_15 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl10_7
    | spl10_15 ),
    inference(subsumption_resolution,[],[f36,f202])).

fof(f202,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_7
    | spl10_15 ),
    inference(backward_demodulation,[],[f143,f93])).

fof(f93,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f143,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl10_15
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f189,plain,
    ( ~ spl10_6
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl10_6
    | spl10_13 ),
    inference(subsumption_resolution,[],[f36,f183])).

fof(f183,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_6
    | spl10_13 ),
    inference(backward_demodulation,[],[f134,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f134,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f147,plain,
    ( ~ spl10_15
    | spl10_16 ),
    inference(avatar_split_clause,[],[f139,f145,f142])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | ~ v1_xboole_0(sK2) ) ),
    inference(resolution,[],[f77,f37])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f74,f38])).

fof(f74,plain,(
    r1_tarski(sK6,sK2) ),
    inference(resolution,[],[f31,f41])).

fof(f31,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f35,f68,f65,f62,f59])).

fof(f35,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:30 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.41  % (20141)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (20140)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (20120)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (20132)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (20123)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (20119)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (20125)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (20118)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (20120)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f355,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f70,f147,f189,f208,f219,f223,f242,f261,f262,f279,f280,f304,f323,f330,f336,f337,f338,f339,f348,f351,f354])).
% 0.20/0.54  fof(f354,plain,(
% 0.20/0.54    spl10_4 | ~spl10_12),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f353])).
% 0.20/0.54  fof(f353,plain,(
% 0.20/0.54    $false | (spl10_4 | ~spl10_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f79,f352])).
% 0.20/0.54  fof(f352,plain,(
% 0.20/0.54    ~r2_hidden(k2_mcart_1(sK8),sK7) | (spl10_4 | ~spl10_12)),
% 0.20/0.54    inference(forward_demodulation,[],[f69,f111])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | ~spl10_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f110])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    spl10_12 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | spl10_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    spl10_4 <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(sK8),sK7)),
% 0.20/0.54    inference(resolution,[],[f52,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.20/0.54    inference(definition_unfolding,[],[f34,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f46,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    (((((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f22,f21,f20,f19,f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  % (20121)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (20126)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (20124)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (20135)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (20147)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (20136)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (20143)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (20142)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (20139)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (20137)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (20128)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (20128)Refutation not found, incomplete strategy% (20128)------------------------------
% 0.20/0.55  % (20128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20128)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20128)Memory used [KB]: 10746
% 0.20/0.55  % (20128)Time elapsed: 0.148 s
% 0.20/0.55  % (20128)------------------------------
% 0.20/0.55  % (20128)------------------------------
% 0.20/0.55  % (20134)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (20144)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (20131)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (20129)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (20122)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.56  % (20129)Refutation not found, incomplete strategy% (20129)------------------------------
% 0.20/0.56  % (20129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (20129)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (20129)Memory used [KB]: 10746
% 0.20/0.56  % (20129)Time elapsed: 0.156 s
% 0.20/0.56  % (20129)------------------------------
% 0.20/0.56  % (20129)------------------------------
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  % (20145)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.20/0.56    inference(flattening,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.20/0.56    inference(negated_conjecture,[],[f9])).
% 0.20/0.56  fof(f9,conjecture,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).
% 0.20/0.56  fof(f351,plain,(
% 0.20/0.56    spl10_3 | ~spl10_11),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f350])).
% 0.20/0.56  fof(f350,plain,(
% 0.20/0.56    $false | (spl10_3 | ~spl10_11)),
% 0.20/0.56    inference(subsumption_resolution,[],[f126,f349])).
% 0.20/0.56  fof(f349,plain,(
% 0.20/0.56    ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | (spl10_3 | ~spl10_11)),
% 0.20/0.56    inference(forward_demodulation,[],[f66,f107])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | ~spl10_11),
% 0.20/0.56    inference(avatar_component_clause,[],[f106])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    spl10_11 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | spl10_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    spl10_3 <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.56  fof(f126,plain,(
% 0.20/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 0.20/0.56    inference(resolution,[],[f78,f45])).
% 0.20/0.56  fof(f78,plain,(
% 0.20/0.56    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.20/0.56    inference(resolution,[],[f52,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f348,plain,(
% 0.20/0.56    spl10_2 | ~spl10_10),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f347])).
% 0.20/0.56  fof(f347,plain,(
% 0.20/0.56    $false | (spl10_2 | ~spl10_10)),
% 0.20/0.56    inference(subsumption_resolution,[],[f167,f346])).
% 0.20/0.56  fof(f346,plain,(
% 0.20/0.56    ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | (spl10_2 | ~spl10_10)),
% 0.20/0.56    inference(backward_demodulation,[],[f63,f103])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | ~spl10_10),
% 0.20/0.56    inference(avatar_component_clause,[],[f102])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    spl10_10 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | spl10_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    spl10_2 <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 0.20/0.56    inference(resolution,[],[f125,f45])).
% 0.20/0.56  fof(f125,plain,(
% 0.20/0.56    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))),
% 0.20/0.56    inference(resolution,[],[f78,f44])).
% 0.20/0.56  fof(f339,plain,(
% 0.20/0.56    spl10_5 | spl10_6 | spl10_7 | spl10_8 | spl10_12),
% 0.20/0.56    inference(avatar_split_clause,[],[f335,f110,f95,f92,f89,f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    spl10_5 <=> k1_xboole_0 = sK0),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    spl10_6 <=> k1_xboole_0 = sK1),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    spl10_7 <=> k1_xboole_0 = sK2),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    spl10_8 <=> k1_xboole_0 = sK3),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.56  fof(f335,plain,(
% 0.20/0.56    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.56    inference(resolution,[],[f53,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(definition_unfolding,[],[f50,f51])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.20/0.56    inference(definition_unfolding,[],[f33,f51])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f338,plain,(
% 0.20/0.56    spl10_5 | spl10_6 | spl10_7 | spl10_8 | spl10_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f334,f106,f95,f92,f89,f86])).
% 0.20/0.56  fof(f334,plain,(
% 0.20/0.56    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.56    inference(resolution,[],[f53,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(definition_unfolding,[],[f49,f51])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f337,plain,(
% 0.20/0.56    spl10_5 | spl10_6 | spl10_7 | spl10_8 | spl10_10),
% 0.20/0.56    inference(avatar_split_clause,[],[f333,f102,f95,f92,f89,f86])).
% 0.20/0.56  fof(f333,plain,(
% 0.20/0.56    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.56    inference(resolution,[],[f53,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(definition_unfolding,[],[f48,f51])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f336,plain,(
% 0.20/0.56    spl10_5 | spl10_6 | spl10_7 | spl10_8 | spl10_9),
% 0.20/0.56    inference(avatar_split_clause,[],[f332,f98,f95,f92,f89,f86])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    spl10_9 <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.56  fof(f332,plain,(
% 0.20/0.56    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.56    inference(resolution,[],[f53,f57])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(definition_unfolding,[],[f47,f51])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f330,plain,(
% 0.20/0.56    ~spl10_20),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f329])).
% 0.20/0.56  fof(f329,plain,(
% 0.20/0.56    $false | ~spl10_20),
% 0.20/0.56    inference(subsumption_resolution,[],[f166,f164])).
% 0.20/0.56  fof(f164,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | ~spl10_20),
% 0.20/0.56    inference(avatar_component_clause,[],[f163])).
% 0.20/0.56  fof(f163,plain,(
% 0.20/0.56    spl10_20 <=> ! [X0] : ~r2_hidden(X0,sK4)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.20/0.56  fof(f166,plain,(
% 0.20/0.56    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 0.20/0.56    inference(resolution,[],[f125,f44])).
% 0.20/0.56  fof(f323,plain,(
% 0.20/0.56    ~spl10_5 | spl10_21),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f322])).
% 0.20/0.56  fof(f322,plain,(
% 0.20/0.56    $false | (~spl10_5 | spl10_21)),
% 0.20/0.56    inference(subsumption_resolution,[],[f36,f320])).
% 0.20/0.56  fof(f320,plain,(
% 0.20/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl10_5 | spl10_21)),
% 0.20/0.56    inference(backward_demodulation,[],[f218,f87])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | ~spl10_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f86])).
% 0.20/0.56  fof(f218,plain,(
% 0.20/0.56    ~v1_xboole_0(sK0) | spl10_21),
% 0.20/0.56    inference(avatar_component_clause,[],[f217])).
% 0.20/0.56  fof(f217,plain,(
% 0.20/0.56    spl10_21 <=> v1_xboole_0(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.56  fof(f304,plain,(
% 0.20/0.56    ~spl10_18),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f303])).
% 0.20/0.56  fof(f303,plain,(
% 0.20/0.56    $false | ~spl10_18),
% 0.20/0.56    inference(subsumption_resolution,[],[f79,f155])).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK7)) ) | ~spl10_18),
% 0.20/0.56    inference(avatar_component_clause,[],[f154])).
% 0.20/0.56  fof(f154,plain,(
% 0.20/0.56    spl10_18 <=> ! [X0] : ~r2_hidden(X0,sK7)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.20/0.56  fof(f280,plain,(
% 0.20/0.56    ~spl10_17 | spl10_18),
% 0.20/0.56    inference(avatar_split_clause,[],[f257,f154,f151])).
% 0.20/0.56  fof(f151,plain,(
% 0.20/0.56    spl10_17 <=> v1_xboole_0(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.20/0.56  fof(f257,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK7) | ~v1_xboole_0(sK3)) )),
% 0.20/0.56    inference(resolution,[],[f113,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.56  fof(f113,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK7)) )),
% 0.20/0.56    inference(resolution,[],[f76,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f25,f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(rectify,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f76,plain,(
% 0.20/0.56    r1_tarski(sK7,sK3)),
% 0.20/0.56    inference(resolution,[],[f32,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.56    inference(nnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f279,plain,(
% 0.20/0.56    ~spl10_14),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f277])).
% 0.20/0.56  fof(f277,plain,(
% 0.20/0.56    $false | ~spl10_14),
% 0.20/0.56    inference(resolution,[],[f167,f137])).
% 0.20/0.56  fof(f137,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK5)) ) | ~spl10_14),
% 0.20/0.56    inference(avatar_component_clause,[],[f136])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    spl10_14 <=> ! [X0] : ~r2_hidden(X0,sK5)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.56  fof(f262,plain,(
% 0.20/0.56    ~spl10_13 | spl10_14),
% 0.20/0.56    inference(avatar_split_clause,[],[f220,f136,f133])).
% 0.20/0.56  fof(f133,plain,(
% 0.20/0.56    spl10_13 <=> v1_xboole_0(sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.56  fof(f220,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK5) | ~v1_xboole_0(sK1)) )),
% 0.20/0.56    inference(resolution,[],[f75,f37])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK5)) )),
% 0.20/0.56    inference(resolution,[],[f73,f38])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    r1_tarski(sK5,sK1)),
% 0.20/0.56    inference(resolution,[],[f30,f41])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f261,plain,(
% 0.20/0.56    spl10_1 | ~spl10_9),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f259])).
% 0.20/0.56  fof(f259,plain,(
% 0.20/0.56    $false | (spl10_1 | ~spl10_9)),
% 0.20/0.56    inference(subsumption_resolution,[],[f254,f166])).
% 0.20/0.56  fof(f254,plain,(
% 0.20/0.56    ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | (spl10_1 | ~spl10_9)),
% 0.20/0.56    inference(backward_demodulation,[],[f60,f99])).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | ~spl10_9),
% 0.20/0.56    inference(avatar_component_clause,[],[f98])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | spl10_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    spl10_1 <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.56  fof(f242,plain,(
% 0.20/0.56    ~spl10_8 | spl10_17),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f241])).
% 0.20/0.56  fof(f241,plain,(
% 0.20/0.56    $false | (~spl10_8 | spl10_17)),
% 0.20/0.56    inference(subsumption_resolution,[],[f36,f236])).
% 0.20/0.56  fof(f236,plain,(
% 0.20/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl10_8 | spl10_17)),
% 0.20/0.56    inference(backward_demodulation,[],[f152,f96])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    k1_xboole_0 = sK3 | ~spl10_8),
% 0.20/0.56    inference(avatar_component_clause,[],[f95])).
% 0.20/0.56  fof(f152,plain,(
% 0.20/0.56    ~v1_xboole_0(sK3) | spl10_17),
% 0.20/0.56    inference(avatar_component_clause,[],[f151])).
% 0.20/0.56  fof(f223,plain,(
% 0.20/0.56    ~spl10_16),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f222])).
% 0.20/0.56  fof(f222,plain,(
% 0.20/0.56    $false | ~spl10_16),
% 0.20/0.56    inference(subsumption_resolution,[],[f126,f146])).
% 0.20/0.56  fof(f146,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK6)) ) | ~spl10_16),
% 0.20/0.56    inference(avatar_component_clause,[],[f145])).
% 0.20/0.56  fof(f145,plain,(
% 0.20/0.56    spl10_16 <=> ! [X0] : ~r2_hidden(X0,sK6)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.20/0.56  fof(f219,plain,(
% 0.20/0.56    ~spl10_21 | spl10_20),
% 0.20/0.56    inference(avatar_split_clause,[],[f214,f163,f217])).
% 0.20/0.56  fof(f214,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK4) | ~v1_xboole_0(sK0)) )),
% 0.20/0.56    inference(resolution,[],[f72,f37])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK4)) )),
% 0.20/0.56    inference(resolution,[],[f71,f38])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    r1_tarski(sK4,sK0)),
% 0.20/0.56    inference(resolution,[],[f29,f41])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f208,plain,(
% 0.20/0.56    ~spl10_7 | spl10_15),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f207])).
% 0.20/0.56  fof(f207,plain,(
% 0.20/0.56    $false | (~spl10_7 | spl10_15)),
% 0.20/0.56    inference(subsumption_resolution,[],[f36,f202])).
% 0.20/0.56  fof(f202,plain,(
% 0.20/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl10_7 | spl10_15)),
% 0.20/0.56    inference(backward_demodulation,[],[f143,f93])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    k1_xboole_0 = sK2 | ~spl10_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f92])).
% 0.20/0.56  fof(f143,plain,(
% 0.20/0.56    ~v1_xboole_0(sK2) | spl10_15),
% 0.20/0.56    inference(avatar_component_clause,[],[f142])).
% 0.20/0.56  fof(f142,plain,(
% 0.20/0.56    spl10_15 <=> v1_xboole_0(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.20/0.56  fof(f189,plain,(
% 0.20/0.56    ~spl10_6 | spl10_13),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f188])).
% 0.20/0.56  fof(f188,plain,(
% 0.20/0.56    $false | (~spl10_6 | spl10_13)),
% 0.20/0.56    inference(subsumption_resolution,[],[f36,f183])).
% 0.20/0.56  fof(f183,plain,(
% 0.20/0.56    ~v1_xboole_0(k1_xboole_0) | (~spl10_6 | spl10_13)),
% 0.20/0.56    inference(backward_demodulation,[],[f134,f90])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | ~spl10_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f89])).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    ~v1_xboole_0(sK1) | spl10_13),
% 0.20/0.56    inference(avatar_component_clause,[],[f133])).
% 0.20/0.56  fof(f147,plain,(
% 0.20/0.56    ~spl10_15 | spl10_16),
% 0.20/0.56    inference(avatar_split_clause,[],[f139,f145,f142])).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK6) | ~v1_xboole_0(sK2)) )),
% 0.20/0.56    inference(resolution,[],[f77,f37])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK6)) )),
% 0.20/0.56    inference(resolution,[],[f74,f38])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    r1_tarski(sK6,sK2)),
% 0.20/0.56    inference(resolution,[],[f31,f41])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ~spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f35,f68,f65,f62,f59])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (20120)------------------------------
% 0.20/0.56  % (20120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (20120)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (20120)Memory used [KB]: 10874
% 0.20/0.56  % (20120)Time elapsed: 0.139 s
% 0.20/0.56  % (20120)------------------------------
% 0.20/0.56  % (20120)------------------------------
% 0.20/0.56  % (20117)Success in time 0.205 s
%------------------------------------------------------------------------------
