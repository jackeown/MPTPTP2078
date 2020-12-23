%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 173 expanded)
%              Number of leaves         :   16 (  69 expanded)
%              Depth                    :    8
%              Number of atoms          :  234 ( 453 expanded)
%              Number of equality atoms :    7 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f45,f51,f60,f78,f87,f93,f101,f132,f149,f156,f179,f191,f198,f222,f233])).

fof(f233,plain,
    ( spl9_7
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f227,f220,f85])).

fof(f85,plain,
    ( spl9_7
  <=> sP4(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f220,plain,
    ( spl9_13
  <=> r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f227,plain,
    ( sP4(sK0,sK2)
    | ~ spl9_13 ),
    inference(resolution,[],[f221,f14])).

fof(f14,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f221,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),sK2)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( spl9_13
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f146,f130,f220])).

fof(f130,plain,
    ( spl9_11
  <=> sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f146,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),sK2)
    | ~ spl9_11 ),
    inference(resolution,[],[f131,f21])).

fof(f21,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f131,plain,
    ( sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f198,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f41,f192])).

fof(f192,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f157,f89])).

fof(f89,plain,
    ( r2_hidden(sK0,k2_relat_1(sK2))
    | ~ spl9_7 ),
    inference(resolution,[],[f86,f28])).

fof(f28,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f86,plain,
    ( sP4(sK0,sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f157,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK2))
    | ~ r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f9,f44])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl9_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK2))
    | ~ r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

fof(f41,plain,
    ( r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl9_2
  <=> r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f191,plain,
    ( spl9_5
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f184,f177,f58])).

fof(f58,plain,
    ( spl9_5
  <=> sP4(sK0,k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f177,plain,
    ( spl9_12
  <=> r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f184,plain,
    ( sP4(sK0,k8_relat_1(sK1,sK2))
    | ~ spl9_12 ),
    inference(resolution,[],[f178,f14])).

fof(f178,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( spl9_12
    | ~ spl9_1
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f174,f99,f32,f177])).

fof(f32,plain,
    ( spl9_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f99,plain,
    ( spl9_9
  <=> sP8(sK0,sK5(sK2,sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f174,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2))
    | ~ spl9_1
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f173,f33])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f173,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2))
    | ~ spl9_1
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f172,f35])).

fof(f35,plain,
    ( ! [X0] : v1_relat_1(k8_relat_1(X0,sK2))
    | ~ spl9_1 ),
    inference(resolution,[],[f33,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f172,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2))
    | ~ spl9_9 ),
    inference(resolution,[],[f100,f30])).

fof(f30,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ sP8(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f100,plain,
    ( sP8(sK0,sK5(sK2,sK0),sK2,sK1)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f156,plain,
    ( spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f82,f109])).

fof(f109,plain,
    ( r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl9_5 ),
    inference(resolution,[],[f59,f28])).

fof(f59,plain,
    ( sP4(sK0,k8_relat_1(sK1,sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f149,plain,
    ( spl9_3
    | ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl9_3
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f145,f104])).

fof(f104,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f145,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl9_11 ),
    inference(resolution,[],[f131,f20])).

fof(f20,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP8(X4,X3,X1,X0)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f132,plain,
    ( spl9_11
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f121,f76,f32,f130])).

fof(f76,plain,
    ( spl9_6
  <=> r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f121,plain,
    ( sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f120,f33])).

fof(f120,plain,
    ( sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f117,f35])).

fof(f117,plain,
    ( ~ v1_relat_1(k8_relat_1(sK1,sK2))
    | sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl9_6 ),
    inference(resolution,[],[f77,f29])).

fof(f29,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | sP8(X4,X3,X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | sP8(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),k8_relat_1(sK1,sK2))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f101,plain,
    ( spl9_9
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f95,f91,f43,f99])).

fof(f91,plain,
    ( spl9_8
  <=> r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f95,plain,
    ( sP8(sK0,sK5(sK2,sK0),sK2,sK1)
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK0),X1)
        | sP8(sK0,X0,X1,sK1) )
    | ~ spl9_3 ),
    inference(resolution,[],[f44,f19])).

fof(f19,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | sP8(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f92,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl9_8
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f88,f85,f91])).

fof(f88,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),sK2)
    | ~ spl9_7 ),
    inference(resolution,[],[f86,f13])).

fof(f13,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f87,plain,
    ( spl9_7
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f80,f49,f85])).

fof(f49,plain,
    ( spl9_4
  <=> r2_hidden(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f80,plain,
    ( sP4(sK0,sK2)
    | ~ spl9_4 ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP4(X2,X0) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,
    ( r2_hidden(sK0,k2_relat_1(sK2))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f78,plain,
    ( spl9_6
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f61,f58,f76])).

fof(f61,plain,
    ( r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),k8_relat_1(sK1,sK2))
    | ~ spl9_5 ),
    inference(resolution,[],[f59,f13])).

fof(f60,plain,
    ( spl9_5
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f55,f40,f58])).

fof(f55,plain,
    ( sP4(sK0,k8_relat_1(sK1,sK2))
    | ~ spl9_2 ),
    inference(resolution,[],[f41,f27])).

fof(f51,plain,
    ( spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f11,f49,f40])).

fof(f11,plain,
    ( r2_hidden(sK0,k2_relat_1(sK2))
    | r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,
    ( spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f10,f43,f40])).

fof(f10,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f12,f32])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:30:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (11225)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (11225)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f34,f45,f51,f60,f78,f87,f93,f101,f132,f149,f156,f179,f191,f198,f222,f233])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    spl9_7 | ~spl9_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f227,f220,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl9_7 <=> sP4(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    spl9_13 <=> r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    sP4(sK0,sK2) | ~spl9_13),
% 0.21/0.49    inference(resolution,[],[f221,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP4(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),sK2) | ~spl9_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f220])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl9_13 | ~spl9_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f146,f130,f220])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl9_11 <=> sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),sK2) | ~spl9_11),
% 0.21/0.49    inference(resolution,[],[f131,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (~sP8(X4,X3,X1,X0) | r2_hidden(k4_tarski(X3,X4),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1) | ~spl9_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ~spl9_2 | ~spl9_3 | ~spl9_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    $false | (~spl9_2 | ~spl9_3 | ~spl9_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f41,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) | (~spl9_3 | ~spl9_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f157,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK2)) | ~spl9_7),
% 0.21/0.49    inference(resolution,[],[f86,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~sP4(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP4(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    sP4(sK0,sK2) | ~spl9_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k2_relat_1(sK2)) | ~r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) | ~spl9_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f9,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1) | ~spl9_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl9_3 <=> r2_hidden(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k2_relat_1(sK2)) | ~r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))) & v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) | ~spl9_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl9_2 <=> r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl9_5 | ~spl9_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f184,f177,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl9_5 <=> sP4(sK0,k8_relat_1(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl9_12 <=> r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    sP4(sK0,k8_relat_1(sK1,sK2)) | ~spl9_12),
% 0.21/0.49    inference(resolution,[],[f178,f14])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2)) | ~spl9_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f177])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl9_12 | ~spl9_1 | ~spl9_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f174,f99,f32,f177])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    spl9_1 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl9_9 <=> sP8(sK0,sK5(sK2,sK0),sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2)) | (~spl9_1 | ~spl9_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f173,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl9_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f32])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2)) | (~spl9_1 | ~spl9_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f172,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) ) | ~spl9_1),
% 0.21/0.49    inference(resolution,[],[f33,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~v1_relat_1(k8_relat_1(sK1,sK2)) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),k8_relat_1(sK1,sK2)) | ~spl9_9),
% 0.21/0.49    inference(resolution,[],[f100,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (~sP8(X4,X3,X1,X0) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | ~sP8(X4,X3,X1,X0) | r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    sP8(sK0,sK5(sK2,sK0),sK2,sK1) | ~spl9_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f99])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl9_2 | ~spl9_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    $false | (spl9_2 | ~spl9_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) | ~spl9_5),
% 0.21/0.49    inference(resolution,[],[f59,f28])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    sP4(sK0,k8_relat_1(sK1,sK2)) | ~spl9_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2))) | spl9_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl9_3 | ~spl9_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    $false | (spl9_3 | ~spl9_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f145,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK1) | spl9_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1) | ~spl9_11),
% 0.21/0.49    inference(resolution,[],[f131,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (~sP8(X4,X3,X1,X0) | r2_hidden(X4,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl9_11 | ~spl9_1 | ~spl9_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f121,f76,f32,f130])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl9_6 <=> r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),k8_relat_1(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1) | (~spl9_1 | ~spl9_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f33])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1) | ~v1_relat_1(sK2) | (~spl9_1 | ~spl9_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f35])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~v1_relat_1(k8_relat_1(sK1,sK2)) | sP8(sK0,sK5(k8_relat_1(sK1,sK2),sK0),sK2,sK1) | ~v1_relat_1(sK2) | ~spl9_6),
% 0.21/0.49    inference(resolution,[],[f77,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1)) | sP8(X4,X3,X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | sP8(X4,X3,X1,X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),k8_relat_1(sK1,sK2)) | ~spl9_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f76])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl9_9 | ~spl9_3 | ~spl9_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f95,f91,f43,f99])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl9_8 <=> r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    sP8(sK0,sK5(sK2,sK0),sK2,sK1) | (~spl9_3 | ~spl9_8)),
% 0.21/0.49    inference(resolution,[],[f92,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK0),X1) | sP8(sK0,X0,X1,sK1)) ) | ~spl9_3),
% 0.21/0.49    inference(resolution,[],[f44,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | sP8(X4,X3,X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),sK2) | ~spl9_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl9_8 | ~spl9_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f88,f85,f91])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(sK2,sK0),sK0),sK2) | ~spl9_7),
% 0.21/0.49    inference(resolution,[],[f86,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~sP4(X2,X0) | r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl9_7 | ~spl9_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f80,f49,f85])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl9_4 <=> r2_hidden(sK0,k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    sP4(sK0,sK2) | ~spl9_4),
% 0.21/0.49    inference(resolution,[],[f50,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP4(X2,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sP4(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK2)) | ~spl9_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl9_6 | ~spl9_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f58,f76])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK5(k8_relat_1(sK1,sK2),sK0),sK0),k8_relat_1(sK1,sK2)) | ~spl9_5),
% 0.21/0.49    inference(resolution,[],[f59,f13])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl9_5 | ~spl9_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f40,f58])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    sP4(sK0,k8_relat_1(sK1,sK2)) | ~spl9_2),
% 0.21/0.49    inference(resolution,[],[f41,f27])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl9_2 | spl9_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f11,f49,f40])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_relat_1(sK2)) | r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl9_2 | spl9_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f10,f43,f40])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    r2_hidden(sK0,sK1) | r2_hidden(sK0,k2_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    spl9_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f12,f32])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11225)------------------------------
% 0.21/0.49  % (11225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11225)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11225)Memory used [KB]: 6268
% 0.21/0.49  % (11225)Time elapsed: 0.092 s
% 0.21/0.49  % (11225)------------------------------
% 0.21/0.49  % (11225)------------------------------
% 0.21/0.49  % (11222)Success in time 0.121 s
%------------------------------------------------------------------------------
