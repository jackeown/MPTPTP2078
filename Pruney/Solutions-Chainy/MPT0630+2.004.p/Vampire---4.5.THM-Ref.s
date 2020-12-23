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
% DateTime   : Thu Dec  3 12:52:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 118 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 489 expanded)
%              Number of equality atoms :   16 (  66 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f114,f233,f242,f246,f275])).

fof(f275,plain,(
    ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f16,f257,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f257,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f247,f54])).

fof(f54,plain,(
    sK2(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK4(sK1,sK2(k2_relat_1(sK1),k1_relat_1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f14,f13,f49,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f49,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),k1_relat_1(sK0)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f16,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
             => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f247,plain,
    ( r2_hidden(k1_funct_1(sK1,sK4(sK1,sK2(k2_relat_1(sK1),k1_relat_1(sK0)))),k1_relat_1(sK0))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f53,f241])).

fof(f241,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl6_16
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f53,plain,(
    r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f14,f13,f49,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f246,plain,(
    spl6_15 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f14,f238])).

fof(f238,plain,
    ( ~ v1_funct_1(sK1)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl6_15
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f242,plain,
    ( ~ spl6_15
    | ~ spl6_2
    | spl6_16
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f234,f231,f240,f74,f236])).

fof(f74,plain,
    ( spl6_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f231,plain,
    ( spl6_14
  <=> ! [X5,X4] :
        ( ~ v1_relat_1(X4)
        | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(X4,sK0)))
        | r2_hidden(k1_funct_1(X4,X5),k1_relat_1(sK0))
        | ~ v1_funct_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
        | ~ v1_funct_1(sK1) )
    | ~ spl6_14 ),
    inference(superposition,[],[f232,f15])).

fof(f15,plain,(
    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f232,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k1_relat_1(k5_relat_1(X4,sK0)))
        | ~ v1_relat_1(X4)
        | r2_hidden(k1_funct_1(X4,X5),k1_relat_1(sK0))
        | ~ v1_funct_1(X4) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( spl6_14
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f45,f107,f231])).

fof(f107,plain,
    ( spl6_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f45,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | r2_hidden(k1_funct_1(X4,X5),k1_relat_1(sK0))
      | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(X4,sK0))) ) ),
    inference(resolution,[],[f18,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f18,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f114,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f17,f109])).

fof(f109,plain,
    ( ~ v1_relat_1(sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f13,f76])).

fof(f76,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 20:19:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.21/0.46  % (26436)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.46  % (26413)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (26413)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f276,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f81,f114,f233,f242,f246,f275])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    ~spl6_16),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f265])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    $false | ~spl6_16),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f16,f257,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    r2_hidden(sK2(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0)) | ~spl6_16),
% 0.21/0.47    inference(forward_demodulation,[],[f247,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    sK2(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK4(sK1,sK2(k2_relat_1(sK1),k1_relat_1(sK0))))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f14,f13,f49,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.47    inference(equality_resolution,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    r2_hidden(sK2(k2_relat_1(sK1),k1_relat_1(sK0)),k2_relat_1(sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f16,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    v1_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f247,plain,(
% 0.21/0.47    r2_hidden(k1_funct_1(sK1,sK4(sK1,sK2(k2_relat_1(sK1),k1_relat_1(sK0)))),k1_relat_1(sK0)) | ~spl6_16),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f53,f241])).
% 0.21/0.47  fof(f241,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl6_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f240])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    spl6_16 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f14,f13,f49,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    spl6_15),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f243])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    $false | spl6_15),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f14,f238])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    ~v1_funct_1(sK1) | spl6_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f236])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    spl6_15 <=> v1_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    ~spl6_15 | ~spl6_2 | spl6_16 | ~spl6_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f234,f231,f240,f74,f236])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl6_2 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    spl6_14 <=> ! [X5,X4] : (~v1_relat_1(X4) | ~r2_hidden(X5,k1_relat_1(k5_relat_1(X4,sK0))) | r2_hidden(k1_funct_1(X4,X5),k1_relat_1(sK0)) | ~v1_funct_1(X4))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.47  fof(f234,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~v1_funct_1(sK1)) ) | ~spl6_14),
% 0.21/0.47    inference(superposition,[],[f232,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    ( ! [X4,X5] : (~r2_hidden(X5,k1_relat_1(k5_relat_1(X4,sK0))) | ~v1_relat_1(X4) | r2_hidden(k1_funct_1(X4,X5),k1_relat_1(sK0)) | ~v1_funct_1(X4)) ) | ~spl6_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f231])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    spl6_14 | ~spl6_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f107,f231])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    spl6_5 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X4,X5] : (~v1_relat_1(sK0) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | r2_hidden(k1_funct_1(X4,X5),k1_relat_1(sK0)) | ~r2_hidden(X5,k1_relat_1(k5_relat_1(X4,sK0)))) )),
% 0.21/0.47    inference(resolution,[],[f18,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    v1_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl6_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    $false | spl6_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f17,f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ~v1_relat_1(sK0) | spl6_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f107])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl6_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    $false | spl6_2),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f13,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (26413)------------------------------
% 0.21/0.47  % (26413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (26413)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (26413)Memory used [KB]: 6396
% 0.21/0.47  % (26413)Time elapsed: 0.057 s
% 0.21/0.47  % (26413)------------------------------
% 0.21/0.47  % (26413)------------------------------
% 0.21/0.47  % (26408)Success in time 0.114 s
%------------------------------------------------------------------------------
