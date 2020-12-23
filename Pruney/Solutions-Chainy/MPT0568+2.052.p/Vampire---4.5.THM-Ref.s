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
% DateTime   : Thu Dec  3 12:50:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  63 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  150 ( 185 expanded)
%              Number of equality atoms :   27 (  32 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f51,f171])).

fof(f171,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f41,f167])).

fof(f167,plain,
    ( ! [X3] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)
    | ~ spl5_3 ),
    inference(resolution,[],[f159,f53])).

fof(f53,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f26,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f35,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f159,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK1(k1_xboole_0,X5,X6),X6)
        | k10_relat_1(k1_xboole_0,X5) = X6 )
    | ~ spl5_3 ),
    inference(resolution,[],[f100,f53])).

fof(f100,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k4_tarski(sK1(k1_xboole_0,X3,X4),sK2(k1_xboole_0,X3,X4)),k1_xboole_0)
        | r2_hidden(sK1(k1_xboole_0,X3,X4),X4)
        | k10_relat_1(k1_xboole_0,X3) = X4 )
    | ~ spl5_3 ),
    inference(resolution,[],[f31,f50])).

fof(f50,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f41,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f51,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f47,f44,f49])).

fof(f44,plain,
    ( spl5_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f47,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f25,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f46,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f42,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (20319)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.43  % (20319)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f174,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f42,f46,f51,f171])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    spl5_1 | ~spl5_3),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.43  fof(f170,plain,(
% 0.21/0.43    $false | (spl5_1 | ~spl5_3)),
% 0.21/0.43    inference(subsumption_resolution,[],[f41,f167])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    ( ! [X3] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)) ) | ~spl5_3),
% 0.21/0.43    inference(resolution,[],[f159,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.43    inference(global_subsumption,[],[f26,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(superposition,[],[f35,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f159,plain,(
% 0.21/0.43    ( ! [X6,X5] : (r2_hidden(sK1(k1_xboole_0,X5,X6),X6) | k10_relat_1(k1_xboole_0,X5) = X6) ) | ~spl5_3),
% 0.21/0.43    inference(resolution,[],[f100,f53])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    ( ! [X4,X3] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,X3,X4),sK2(k1_xboole_0,X3,X4)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,X3,X4),X4) | k10_relat_1(k1_xboole_0,X3) = X4) ) | ~spl5_3),
% 0.21/0.43    inference(resolution,[],[f31,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl5_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl5_3 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(rectify,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl5_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl5_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl5_3 | ~spl5_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f47,f44,f49])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl5_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl5_2),
% 0.21/0.43    inference(superposition,[],[f25,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl5_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl5_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f44])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ~spl5_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f40])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (20319)------------------------------
% 0.21/0.43  % (20319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (20319)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (20319)Memory used [KB]: 10746
% 0.21/0.43  % (20319)Time elapsed: 0.011 s
% 0.21/0.43  % (20319)------------------------------
% 0.21/0.43  % (20319)------------------------------
% 0.21/0.44  % (20312)Success in time 0.079 s
%------------------------------------------------------------------------------
