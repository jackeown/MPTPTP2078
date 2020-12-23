%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 178 expanded)
%              Number of leaves         :   17 (  78 expanded)
%              Depth                    :    7
%              Number of atoms          :  245 ( 575 expanded)
%              Number of equality atoms :   12 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f69,f95,f108,f130,f136,f139,f144,f155,f164,f169,f172,f175])).

fof(f175,plain,
    ( spl5_12
    | ~ spl5_3
    | ~ spl5_1
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f174,f160,f25,f35,f101])).

fof(f101,plain,
    ( spl5_12
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f35,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f25,plain,
    ( spl5_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f160,plain,
    ( spl5_19
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f174,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | ~ spl5_19 ),
    inference(resolution,[],[f161,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f161,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f172,plain,
    ( spl5_2
    | spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f171,f43,f47,f30])).

fof(f30,plain,
    ( spl5_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f47,plain,
    ( spl5_5
  <=> r2_hidden(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f43,plain,
    ( spl5_4
  <=> r2_hidden(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f171,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | sK1 = sK2
    | spl5_4 ),
    inference(resolution,[],[f44,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f44,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f169,plain,
    ( spl5_10
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f167,f152,f35,f25,f88])).

fof(f88,plain,
    ( spl5_10
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f152,plain,
    ( spl5_18
  <=> r2_hidden(sK3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f167,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ spl5_18 ),
    inference(resolution,[],[f154,f20])).

fof(f154,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f164,plain,
    ( spl5_19
    | ~ spl5_16
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f158,f105,f133,f160])).

fof(f133,plain,
    ( spl5_16
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f105,plain,
    ( spl5_13
  <=> m1_subset_1(sK3(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f158,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl5_13 ),
    inference(resolution,[],[f107,f13])).

fof(f13,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f107,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f155,plain,
    ( ~ spl5_17
    | spl5_18
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f149,f92,f152,f141])).

fof(f141,plain,
    ( spl5_17
  <=> r2_hidden(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f92,plain,
    ( spl5_11
  <=> m1_subset_1(sK3(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f149,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK2)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | ~ spl5_11 ),
    inference(resolution,[],[f94,f14])).

fof(f14,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f144,plain,
    ( spl5_10
    | spl5_17
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f121,f35,f25,f141,f88])).

fof(f121,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),sK1)
    | r1_tarski(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(sK3(sK0,sK1,X0),sK1)
        | r1_tarski(sK1,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f19,f27])).

fof(f27,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f139,plain,
    ( spl5_5
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f138,f88,f43,f47])).

fof(f138,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(resolution,[],[f45,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK2) )
    | ~ spl5_10 ),
    inference(resolution,[],[f90,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f90,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f45,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f136,plain,
    ( spl5_12
    | spl5_16
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f124,f35,f25,f133,f101])).

fof(f124,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | r1_tarski(sK2,sK1)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f75,f27])).

fof(f75,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(sK3(sK0,sK2,X1),sK2)
        | r1_tarski(sK2,X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f19,f37])).

fof(f130,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f128,f101,f47,f43])).

fof(f128,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(resolution,[],[f118,f49])).

fof(f49,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,sK1) )
    | ~ spl5_12 ),
    inference(resolution,[],[f103,f23])).

fof(f103,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,
    ( spl5_12
    | spl5_13
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f98,f35,f25,f105,f101])).

fof(f98,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),sK0)
    | r1_tarski(sK2,sK1)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f72,f27])).

fof(f72,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | m1_subset_1(sK3(sK0,sK2,X1),sK0)
        | r1_tarski(sK2,X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f18,f37])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,
    ( spl5_10
    | spl5_11
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f77,f35,f25,f92,f88])).

fof(f77,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),sK0)
    | r1_tarski(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f71,f37])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | m1_subset_1(sK3(sK0,sK1,X0),sK0)
        | r1_tarski(sK1,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f18,f27])).

fof(f69,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f64,f47,f43,f30])).

fof(f64,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | sK1 = sK2
    | ~ spl5_5 ),
    inference(resolution,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:38:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.54  % (16297)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.54  % (16289)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.55  % (16287)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.55  % (16303)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.55  % (16297)Refutation found. Thanks to Tanya!
% 0.19/0.55  % SZS status Theorem for theBenchmark
% 0.19/0.55  % (16305)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.56  % (16295)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.56  % SZS output start Proof for theBenchmark
% 0.19/0.56  fof(f176,plain,(
% 0.19/0.56    $false),
% 0.19/0.56    inference(avatar_sat_refutation,[],[f28,f33,f38,f69,f95,f108,f130,f136,f139,f144,f155,f164,f169,f172,f175])).
% 0.19/0.56  fof(f175,plain,(
% 0.19/0.56    spl5_12 | ~spl5_3 | ~spl5_1 | ~spl5_19),
% 0.19/0.56    inference(avatar_split_clause,[],[f174,f160,f25,f35,f101])).
% 0.19/0.56  fof(f101,plain,(
% 0.19/0.56    spl5_12 <=> r1_tarski(sK2,sK1)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.56  fof(f35,plain,(
% 0.19/0.56    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.56  fof(f25,plain,(
% 0.19/0.56    spl5_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.56  fof(f160,plain,(
% 0.19/0.56    spl5_19 <=> r2_hidden(sK3(sK0,sK2,sK1),sK1)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.19/0.56  fof(f174,plain,(
% 0.19/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1) | ~spl5_19),
% 0.19/0.56    inference(resolution,[],[f161,f20])).
% 0.19/0.56  fof(f20,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f10])).
% 0.19/0.56  fof(f10,plain,(
% 0.19/0.56    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.56    inference(flattening,[],[f9])).
% 0.19/0.56  fof(f9,plain,(
% 0.19/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f3])).
% 0.19/0.57  fof(f3,axiom,(
% 0.19/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.19/0.57  fof(f161,plain,(
% 0.19/0.57    r2_hidden(sK3(sK0,sK2,sK1),sK1) | ~spl5_19),
% 0.19/0.57    inference(avatar_component_clause,[],[f160])).
% 0.19/0.57  fof(f172,plain,(
% 0.19/0.57    spl5_2 | spl5_5 | spl5_4),
% 0.19/0.57    inference(avatar_split_clause,[],[f171,f43,f47,f30])).
% 0.19/0.57  fof(f30,plain,(
% 0.19/0.57    spl5_2 <=> sK1 = sK2),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.57  fof(f47,plain,(
% 0.19/0.57    spl5_5 <=> r2_hidden(sK4(sK1,sK2),sK2)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.57  fof(f43,plain,(
% 0.19/0.57    spl5_4 <=> r2_hidden(sK4(sK1,sK2),sK1)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.57  fof(f171,plain,(
% 0.19/0.57    r2_hidden(sK4(sK1,sK2),sK2) | sK1 = sK2 | spl5_4),
% 0.19/0.57    inference(resolution,[],[f44,f21])).
% 0.19/0.57  fof(f21,plain,(
% 0.19/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.19/0.57    inference(cnf_transformation,[],[f11])).
% 0.19/0.57  fof(f11,plain,(
% 0.19/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.19/0.57    inference(ennf_transformation,[],[f2])).
% 0.19/0.57  fof(f2,axiom,(
% 0.19/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.19/0.57  fof(f44,plain,(
% 0.19/0.57    ~r2_hidden(sK4(sK1,sK2),sK1) | spl5_4),
% 0.19/0.57    inference(avatar_component_clause,[],[f43])).
% 0.19/0.57  fof(f169,plain,(
% 0.19/0.57    spl5_10 | ~spl5_1 | ~spl5_3 | ~spl5_18),
% 0.19/0.57    inference(avatar_split_clause,[],[f167,f152,f35,f25,f88])).
% 0.19/0.57  fof(f88,plain,(
% 0.19/0.57    spl5_10 <=> r1_tarski(sK1,sK2)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.19/0.57  fof(f152,plain,(
% 0.19/0.57    spl5_18 <=> r2_hidden(sK3(sK0,sK1,sK2),sK2)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.19/0.57  fof(f167,plain,(
% 0.19/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK2) | ~spl5_18),
% 0.19/0.57    inference(resolution,[],[f154,f20])).
% 0.19/0.57  fof(f154,plain,(
% 0.19/0.57    r2_hidden(sK3(sK0,sK1,sK2),sK2) | ~spl5_18),
% 0.19/0.57    inference(avatar_component_clause,[],[f152])).
% 0.19/0.57  fof(f164,plain,(
% 0.19/0.57    spl5_19 | ~spl5_16 | ~spl5_13),
% 0.19/0.57    inference(avatar_split_clause,[],[f158,f105,f133,f160])).
% 0.19/0.57  fof(f133,plain,(
% 0.19/0.57    spl5_16 <=> r2_hidden(sK3(sK0,sK2,sK1),sK2)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.19/0.57  fof(f105,plain,(
% 0.19/0.57    spl5_13 <=> m1_subset_1(sK3(sK0,sK2,sK1),sK0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.19/0.57  fof(f158,plain,(
% 0.19/0.57    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | r2_hidden(sK3(sK0,sK2,sK1),sK1) | ~spl5_13),
% 0.19/0.57    inference(resolution,[],[f107,f13])).
% 0.19/0.57  fof(f13,plain,(
% 0.19/0.57    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f8])).
% 0.19/0.57  fof(f8,plain,(
% 0.19/0.57    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.57    inference(flattening,[],[f7])).
% 0.19/0.57  fof(f7,plain,(
% 0.19/0.57    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.57    inference(ennf_transformation,[],[f5])).
% 0.19/0.57  fof(f5,negated_conjecture,(
% 0.19/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.19/0.57    inference(negated_conjecture,[],[f4])).
% 0.19/0.57  fof(f4,conjecture,(
% 0.19/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.19/0.57  fof(f107,plain,(
% 0.19/0.57    m1_subset_1(sK3(sK0,sK2,sK1),sK0) | ~spl5_13),
% 0.19/0.57    inference(avatar_component_clause,[],[f105])).
% 0.19/0.57  fof(f155,plain,(
% 0.19/0.57    ~spl5_17 | spl5_18 | ~spl5_11),
% 0.19/0.57    inference(avatar_split_clause,[],[f149,f92,f152,f141])).
% 0.19/0.57  fof(f141,plain,(
% 0.19/0.57    spl5_17 <=> r2_hidden(sK3(sK0,sK1,sK2),sK1)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.19/0.57  fof(f92,plain,(
% 0.19/0.57    spl5_11 <=> m1_subset_1(sK3(sK0,sK1,sK2),sK0)),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.19/0.57  fof(f149,plain,(
% 0.19/0.57    r2_hidden(sK3(sK0,sK1,sK2),sK2) | ~r2_hidden(sK3(sK0,sK1,sK2),sK1) | ~spl5_11),
% 0.19/0.57    inference(resolution,[],[f94,f14])).
% 0.19/0.57  fof(f14,plain,(
% 0.19/0.57    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f8])).
% 0.19/0.57  fof(f94,plain,(
% 0.19/0.57    m1_subset_1(sK3(sK0,sK1,sK2),sK0) | ~spl5_11),
% 0.19/0.57    inference(avatar_component_clause,[],[f92])).
% 0.19/0.57  fof(f144,plain,(
% 0.19/0.57    spl5_10 | spl5_17 | ~spl5_1 | ~spl5_3),
% 0.19/0.57    inference(avatar_split_clause,[],[f121,f35,f25,f141,f88])).
% 0.19/0.57  fof(f121,plain,(
% 0.19/0.57    r2_hidden(sK3(sK0,sK1,sK2),sK1) | r1_tarski(sK1,sK2) | (~spl5_1 | ~spl5_3)),
% 0.19/0.57    inference(resolution,[],[f74,f37])).
% 0.19/0.57  fof(f37,plain,(
% 0.19/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl5_3),
% 0.19/0.57    inference(avatar_component_clause,[],[f35])).
% 0.19/0.57  fof(f74,plain,(
% 0.19/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(sK3(sK0,sK1,X0),sK1) | r1_tarski(sK1,X0)) ) | ~spl5_1),
% 0.19/0.57    inference(resolution,[],[f19,f27])).
% 0.19/0.57  fof(f27,plain,(
% 0.19/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_1),
% 0.19/0.57    inference(avatar_component_clause,[],[f25])).
% 0.19/0.57  fof(f19,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f10])).
% 0.19/0.57  fof(f139,plain,(
% 0.19/0.57    spl5_5 | ~spl5_4 | ~spl5_10),
% 0.19/0.57    inference(avatar_split_clause,[],[f138,f88,f43,f47])).
% 0.19/0.57  fof(f138,plain,(
% 0.19/0.57    r2_hidden(sK4(sK1,sK2),sK2) | (~spl5_4 | ~spl5_10)),
% 0.19/0.57    inference(resolution,[],[f45,f97])).
% 0.19/0.57  fof(f97,plain,(
% 0.19/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) ) | ~spl5_10),
% 0.19/0.57    inference(resolution,[],[f90,f23])).
% 0.19/0.57  fof(f23,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f12])).
% 0.19/0.57  fof(f12,plain,(
% 0.19/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f6])).
% 0.19/0.57  fof(f6,plain,(
% 0.19/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.57  fof(f1,axiom,(
% 0.19/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.57  fof(f90,plain,(
% 0.19/0.57    r1_tarski(sK1,sK2) | ~spl5_10),
% 0.19/0.57    inference(avatar_component_clause,[],[f88])).
% 0.19/0.57  fof(f45,plain,(
% 0.19/0.57    r2_hidden(sK4(sK1,sK2),sK1) | ~spl5_4),
% 0.19/0.57    inference(avatar_component_clause,[],[f43])).
% 0.19/0.57  fof(f136,plain,(
% 0.19/0.57    spl5_12 | spl5_16 | ~spl5_1 | ~spl5_3),
% 0.19/0.57    inference(avatar_split_clause,[],[f124,f35,f25,f133,f101])).
% 0.19/0.57  fof(f124,plain,(
% 0.19/0.57    r2_hidden(sK3(sK0,sK2,sK1),sK2) | r1_tarski(sK2,sK1) | (~spl5_1 | ~spl5_3)),
% 0.19/0.57    inference(resolution,[],[f75,f27])).
% 0.19/0.57  fof(f75,plain,(
% 0.19/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(sK3(sK0,sK2,X1),sK2) | r1_tarski(sK2,X1)) ) | ~spl5_3),
% 0.19/0.57    inference(resolution,[],[f19,f37])).
% 0.19/0.57  fof(f130,plain,(
% 0.19/0.57    spl5_4 | ~spl5_5 | ~spl5_12),
% 0.19/0.57    inference(avatar_split_clause,[],[f128,f101,f47,f43])).
% 0.19/0.57  fof(f128,plain,(
% 0.19/0.57    r2_hidden(sK4(sK1,sK2),sK1) | (~spl5_5 | ~spl5_12)),
% 0.19/0.57    inference(resolution,[],[f118,f49])).
% 0.19/0.57  fof(f49,plain,(
% 0.19/0.57    r2_hidden(sK4(sK1,sK2),sK2) | ~spl5_5),
% 0.19/0.57    inference(avatar_component_clause,[],[f47])).
% 0.19/0.57  fof(f118,plain,(
% 0.19/0.57    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1)) ) | ~spl5_12),
% 0.19/0.57    inference(resolution,[],[f103,f23])).
% 0.19/0.57  fof(f103,plain,(
% 0.19/0.57    r1_tarski(sK2,sK1) | ~spl5_12),
% 0.19/0.57    inference(avatar_component_clause,[],[f101])).
% 0.19/0.57  fof(f108,plain,(
% 0.19/0.57    spl5_12 | spl5_13 | ~spl5_1 | ~spl5_3),
% 0.19/0.57    inference(avatar_split_clause,[],[f98,f35,f25,f105,f101])).
% 0.19/0.57  fof(f98,plain,(
% 0.19/0.57    m1_subset_1(sK3(sK0,sK2,sK1),sK0) | r1_tarski(sK2,sK1) | (~spl5_1 | ~spl5_3)),
% 0.19/0.57    inference(resolution,[],[f72,f27])).
% 0.19/0.57  fof(f72,plain,(
% 0.19/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | m1_subset_1(sK3(sK0,sK2,X1),sK0) | r1_tarski(sK2,X1)) ) | ~spl5_3),
% 0.19/0.57    inference(resolution,[],[f18,f37])).
% 0.19/0.57  fof(f18,plain,(
% 0.19/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f10])).
% 0.19/0.57  fof(f95,plain,(
% 0.19/0.57    spl5_10 | spl5_11 | ~spl5_1 | ~spl5_3),
% 0.19/0.57    inference(avatar_split_clause,[],[f77,f35,f25,f92,f88])).
% 0.19/0.57  fof(f77,plain,(
% 0.19/0.57    m1_subset_1(sK3(sK0,sK1,sK2),sK0) | r1_tarski(sK1,sK2) | (~spl5_1 | ~spl5_3)),
% 0.19/0.57    inference(resolution,[],[f71,f37])).
% 0.19/0.57  fof(f71,plain,(
% 0.19/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | m1_subset_1(sK3(sK0,sK1,X0),sK0) | r1_tarski(sK1,X0)) ) | ~spl5_1),
% 0.19/0.57    inference(resolution,[],[f18,f27])).
% 0.19/0.57  fof(f69,plain,(
% 0.19/0.57    spl5_2 | ~spl5_4 | ~spl5_5),
% 0.19/0.57    inference(avatar_split_clause,[],[f64,f47,f43,f30])).
% 0.19/0.57  fof(f64,plain,(
% 0.19/0.57    ~r2_hidden(sK4(sK1,sK2),sK1) | sK1 = sK2 | ~spl5_5),
% 0.19/0.57    inference(resolution,[],[f22,f49])).
% 0.19/0.57  fof(f22,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.19/0.57    inference(cnf_transformation,[],[f11])).
% 0.19/0.57  fof(f38,plain,(
% 0.19/0.57    spl5_3),
% 0.19/0.57    inference(avatar_split_clause,[],[f15,f35])).
% 0.19/0.57  fof(f15,plain,(
% 0.19/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.57    inference(cnf_transformation,[],[f8])).
% 0.19/0.57  fof(f33,plain,(
% 0.19/0.57    ~spl5_2),
% 0.19/0.57    inference(avatar_split_clause,[],[f16,f30])).
% 0.19/0.57  fof(f16,plain,(
% 0.19/0.57    sK1 != sK2),
% 0.19/0.57    inference(cnf_transformation,[],[f8])).
% 0.19/0.57  fof(f28,plain,(
% 0.19/0.57    spl5_1),
% 0.19/0.57    inference(avatar_split_clause,[],[f17,f25])).
% 0.19/0.57  fof(f17,plain,(
% 0.19/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.57    inference(cnf_transformation,[],[f8])).
% 0.19/0.57  % SZS output end Proof for theBenchmark
% 0.19/0.57  % (16297)------------------------------
% 0.19/0.57  % (16297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (16297)Termination reason: Refutation
% 0.19/0.57  
% 0.19/0.57  % (16297)Memory used [KB]: 10746
% 0.19/0.57  % (16297)Time elapsed: 0.137 s
% 0.19/0.57  % (16297)------------------------------
% 0.19/0.57  % (16297)------------------------------
% 0.19/0.57  % (16280)Success in time 0.221 s
%------------------------------------------------------------------------------
