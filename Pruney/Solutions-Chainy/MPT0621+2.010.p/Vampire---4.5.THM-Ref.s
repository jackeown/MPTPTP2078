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
% DateTime   : Thu Dec  3 12:51:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 102 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  252 ( 478 expanded)
%              Number of equality atoms :   92 ( 184 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f148,f152,f160,f167])).

fof(f167,plain,
    ( spl10_1
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl10_1
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f72,f144,f159,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f159,plain,
    ( v1_relat_1(sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl10_9
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f144,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl10_7
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f72,plain,
    ( k1_xboole_0 != sK0
    | spl10_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f160,plain,
    ( spl10_9
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f154,f143,f157])).

fof(f154,plain,
    ( v1_relat_1(sK0)
    | ~ spl10_7 ),
    inference(resolution,[],[f144,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

% (13698)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f31,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK5(X0)
          & r2_hidden(sK5(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK6(X4),sK7(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK5(X0)
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK6(X4),sK7(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f152,plain,
    ( spl10_1
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl10_1
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f72,f48,f49,f147])).

fof(f147,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK4(sK0,X1))
        | ~ v1_relat_1(sK4(sK0,X1))
        | k1_xboole_0 = X1 )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl10_8
  <=> ! [X1] :
        ( k1_xboole_0 = X1
        | ~ v1_relat_1(sK4(sK0,X1))
        | ~ v1_funct_1(sK4(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f49,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f148,plain,
    ( spl10_7
    | spl10_8 ),
    inference(avatar_split_clause,[],[f139,f146,f143])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK4(sK0,X1))
      | ~ v1_relat_1(sK4(sK0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK4(sK0,X1))
      | ~ v1_relat_1(sK4(sK0,X1)) ) ),
    inference(superposition,[],[f45,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1(sK0),X1) = X0
      | ~ r2_hidden(X1,sK0)
      | ~ v1_funct_1(sK4(sK0,X0))
      | ~ v1_relat_1(sK4(sK0,X0)) ) ),
    inference(superposition,[],[f51,f130])).

fof(f130,plain,(
    ! [X0] :
      ( sK1(sK0) = sK4(sK0,X0)
      | ~ v1_funct_1(sK4(sK0,X0))
      | ~ v1_relat_1(sK4(sK0,X0)) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0) = sK4(sK0,X1)
      | ~ v1_funct_1(sK4(sK0,X1))
      | ~ v1_relat_1(sK4(sK0,X1)) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X1
      | sK1(X0) = sK4(X1,X2)
      | sK0 != X0
      | ~ v1_funct_1(sK4(X1,X2))
      | ~ v1_relat_1(sK4(X1,X2)) ) ),
    inference(global_subsumption,[],[f42,f43,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK1(X0) = sK4(X1,X2)
      | sK0 != X1
      | ~ v1_funct_1(sK4(X1,X2))
      | ~ v1_relat_1(sK4(X1,X2))
      | ~ v1_funct_1(sK1(X0))
      | ~ v1_relat_1(sK1(X0)) ) ),
    inference(superposition,[],[f89,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( sK0 != k1_relat_1(X4)
      | sK4(X2,X3) = X4
      | sK0 != X2
      | ~ v1_funct_1(sK4(X2,X3))
      | ~ v1_relat_1(sK4(X2,X3))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f40,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | X1 = X2
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f43,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f41,f70])).

fof(f41,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (13714)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.48  % (13706)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.49  % (13714)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f73,f148,f152,f160,f167])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl10_1 | ~spl10_7 | ~spl10_9),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    $false | (spl10_1 | ~spl10_7 | ~spl10_9)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f72,f144,f159,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    v1_relat_1(sK0) | ~spl10_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f157])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl10_9 <=> v1_relat_1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl10_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl10_7 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    k1_xboole_0 != sK0 | spl10_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl10_1 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl10_9 | ~spl10_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f154,f143,f157])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    v1_relat_1(sK0) | ~spl10_7),
% 0.20/0.49    inference(resolution,[],[f144,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  % (13698)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK5(X0) & r2_hidden(sK5(X0),X0))) & (! [X4] : (k4_tarski(sK6(X4),sK7(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f30,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK5(X0) & r2_hidden(sK5(X0),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK6(X4),sK7(X4)) = X4)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(rectify,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl10_1 | ~spl10_8),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f149])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    $false | (spl10_1 | ~spl10_8)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f72,f48,f49,f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ( ! [X1] : (~v1_funct_1(sK4(sK0,X1)) | ~v1_relat_1(sK4(sK0,X1)) | k1_xboole_0 = X1) ) | ~spl10_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f146])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    spl10_8 <=> ! [X1] : (k1_xboole_0 = X1 | ~v1_relat_1(sK4(sK0,X1)) | ~v1_funct_1(sK4(sK0,X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    spl10_7 | spl10_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f139,f146,f143])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X0,sK0) | ~v1_funct_1(sK4(sK0,X1)) | ~v1_relat_1(sK4(sK0,X1))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK0) | ~v1_funct_1(sK4(sK0,X1)) | ~v1_relat_1(sK4(sK0,X1))) )),
% 0.20/0.49    inference(superposition,[],[f45,f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_funct_1(sK1(sK0),X1) = X0 | ~r2_hidden(X1,sK0) | ~v1_funct_1(sK4(sK0,X0)) | ~v1_relat_1(sK4(sK0,X0))) )),
% 0.20/0.49    inference(superposition,[],[f51,f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0] : (sK1(sK0) = sK4(sK0,X0) | ~v1_funct_1(sK4(sK0,X0)) | ~v1_relat_1(sK4(sK0,X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f129])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK0 != X0 | sK1(X0) = sK4(sK0,X1) | ~v1_funct_1(sK4(sK0,X1)) | ~v1_relat_1(sK4(sK0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sK0 != X1 | sK1(X0) = sK4(X1,X2) | sK0 != X0 | ~v1_funct_1(sK4(X1,X2)) | ~v1_relat_1(sK4(X1,X2))) )),
% 0.20/0.49    inference(global_subsumption,[],[f42,f43,f120])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sK0 != X0 | sK1(X0) = sK4(X1,X2) | sK0 != X1 | ~v1_funct_1(sK4(X1,X2)) | ~v1_relat_1(sK4(X1,X2)) | ~v1_funct_1(sK1(X0)) | ~v1_relat_1(sK1(X0))) )),
% 0.20/0.49    inference(superposition,[],[f89,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (sK0 != k1_relat_1(X4) | sK4(X2,X3) = X4 | sK0 != X2 | ~v1_funct_1(sK4(X2,X3)) | ~v1_relat_1(sK4(X2,X3)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) )),
% 0.20/0.49    inference(superposition,[],[f40,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | X1 = X2 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~spl10_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f70])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    k1_xboole_0 != sK0),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (13714)------------------------------
% 0.20/0.49  % (13714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13714)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (13714)Memory used [KB]: 10746
% 0.20/0.49  % (13714)Time elapsed: 0.063 s
% 0.20/0.49  % (13714)------------------------------
% 0.20/0.49  % (13714)------------------------------
% 0.20/0.50  % (13690)Success in time 0.139 s
%------------------------------------------------------------------------------
