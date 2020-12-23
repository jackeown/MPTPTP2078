%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 184 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  242 (1132 expanded)
%              Number of equality atoms :   18 ( 119 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f100,f114])).

fof(f114,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f112,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f112,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f111,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f111,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f52,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f108,plain,
    ( r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl5_2 ),
    inference(resolution,[],[f106,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK3(X0,X1,X2),X2)
            & r2_hidden(sK3(X0,X1,X2),X1)
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f106,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f105,f52])).

fof(f105,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | r1_tarski(sK2,sK1)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f104,f17])).

fof(f104,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f103,f18])).

fof(f103,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | spl5_2 ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl5_2 ),
    inference(resolution,[],[f83,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK2,sK1),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ r2_hidden(sK3(X0,sK2,sK1),sK2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | spl5_2 ),
    inference(resolution,[],[f65,f20])).

fof(f20,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(X1,sK2,sK1),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X1)) )
    | spl5_2 ),
    inference(resolution,[],[f24,f52])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f100,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f98,f17])).

fof(f98,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f97,f18])).

fof(f97,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f94,f48])).

% (15957)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f48,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl5_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f94,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(resolution,[],[f92,f23])).

fof(f92,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f91,f48])).

fof(f91,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | r1_tarski(sK1,sK2)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f90,f18])).

fof(f90,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f89,f17])).

fof(f89,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(resolution,[],[f74,f22])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK1,sK2),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ r2_hidden(sK3(X0,sK1,sK2),sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | spl5_1 ),
    inference(resolution,[],[f64,f19])).

fof(f19,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,sK1,sK2),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | spl5_1 ),
    inference(resolution,[],[f24,f48])).

fof(f53,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f42,f50,f46])).

fof(f42,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f32,f31])).

fof(f31,plain,(
    ~ sQ4_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f21,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (15958)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (15950)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (15958)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (15945)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f53,f100,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    $false | spl5_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f112,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11,f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f5])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.48    inference(negated_conjecture,[],[f3])).
% 0.20/0.48  fof(f3,conjecture,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl5_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f111,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl5_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f108,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ~r1_tarski(sK2,sK1) | spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl5_2 <=> r1_tarski(sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl5_2),
% 0.20/0.48    inference(resolution,[],[f106,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | spl5_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f105,f52])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | r1_tarski(sK2,sK1) | spl5_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f104,f17])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1) | spl5_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f103,f18])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1) | spl5_2),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl5_2),
% 0.20/0.48    inference(resolution,[],[f83,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK3(X0,sK2,sK1),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,sK2,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | spl5_2),
% 0.20/0.48    inference(resolution,[],[f65,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X3] : (r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2) | ~m1_subset_1(X3,sK0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(sK3(X1,sK2,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(X1))) ) | spl5_2),
% 0.20/0.48    inference(resolution,[],[f24,f52])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl5_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    $false | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f17])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f97,f18])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f94,f48])).
% 0.20/0.48  % (15957)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ~r1_tarski(sK1,sK2) | spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    spl5_1 <=> r1_tarski(sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl5_1),
% 0.20/0.48    inference(resolution,[],[f92,f23])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f91,f48])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | r1_tarski(sK1,sK2) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f90,f18])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2) | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f17])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2) | spl5_1),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl5_1),
% 0.20/0.48    inference(resolution,[],[f74,f22])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK3(X0,sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,sK1,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) ) | spl5_1),
% 0.20/0.48    inference(resolution,[],[f64,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(sK3(X0,sK1,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0))) ) | spl5_1),
% 0.20/0.48    inference(resolution,[],[f24,f48])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ~spl5_1 | ~spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f50,f46])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ~r1_tarski(sK2,sK1) | ~r1_tarski(sK1,sK2)),
% 0.20/0.48    inference(resolution,[],[f32,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ~sQ4_eqProxy(sK1,sK2)),
% 0.20/0.48    inference(equality_proxy_replacement,[],[f21,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    sK1 != sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sQ4_eqProxy(X0,X1) | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(equality_proxy_replacement,[],[f27,f30])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (15958)------------------------------
% 0.20/0.48  % (15958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15958)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (15958)Memory used [KB]: 6140
% 0.20/0.48  % (15958)Time elapsed: 0.075 s
% 0.20/0.48  % (15958)------------------------------
% 0.20/0.48  % (15958)------------------------------
% 0.20/0.48  % (15943)Success in time 0.129 s
%------------------------------------------------------------------------------
