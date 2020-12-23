%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  91 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 192 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f53,f74,f84,f90,f101])).

fof(f101,plain,
    ( ~ spl5_3
    | ~ spl5_6
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_6
    | spl5_8 ),
    inference(global_subsumption,[],[f92,f95])).

fof(f95,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))))
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f52,f73,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f73,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK4))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_6
  <=> r1_tarski(k2_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f52,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),k2_zfmisc_1(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_3
  <=> ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f92,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))))
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f89,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f89,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_8
  <=> r2_hidden(sK0,k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f90,plain,
    ( ~ spl5_8
    | spl5_7 ),
    inference(avatar_split_clause,[],[f85,f81,f87])).

fof(f81,plain,
    ( spl5_7
  <=> r2_hidden(sK0,k2_zfmisc_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f85,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))))
    | spl5_7 ),
    inference(forward_demodulation,[],[f83,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f30,f24,f24,f24])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f83,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f84,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f31,f81])).

fof(f31,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))) ),
    inference(definition_unfolding,[],[f21,f24,f24])).

fof(f21,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
    & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
        & r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
      & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(f74,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f64,f44,f71])).

fof(f44,plain,
    ( spl5_2
  <=> r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f64,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK4))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f46,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f53,plain,
    ( spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f48,f39,f51])).

fof(f39,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f48,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_tarski(sK0,X0),k2_zfmisc_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f41,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f47,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:22:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (4377)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.42  % (4372)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.43  % (4377)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f42,f47,f53,f74,f84,f90,f101])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    ~spl5_3 | ~spl5_6 | spl5_8),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f100])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    $false | (~spl5_3 | ~spl5_6 | spl5_8)),
% 0.20/0.43    inference(global_subsumption,[],[f92,f95])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    ~r1_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))) | (~spl5_3 | ~spl5_6)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f52,f73,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f28,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    r1_tarski(k2_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK4)) | ~spl5_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl5_6 <=> r1_tarski(k2_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK4))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK0,X0),k2_zfmisc_1(sK1,sK2))) ) | ~spl5_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl5_3 <=> ! [X0] : ~r1_xboole_0(k2_tarski(sK0,X0),k2_zfmisc_1(sK1,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    r1_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))) | spl5_8),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f89,f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f25,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    ~r2_hidden(sK0,k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))) | spl5_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f87])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl5_8 <=> r2_hidden(sK0,k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ~spl5_8 | spl5_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f85,f81,f87])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl5_7 <=> r2_hidden(sK0,k2_zfmisc_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    ~r2_hidden(sK0,k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))) | spl5_7),
% 0.20/0.43    inference(forward_demodulation,[],[f83,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f30,f24,f24,f24])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ~r2_hidden(sK0,k2_zfmisc_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)))) | spl5_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ~spl5_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f81])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ~r2_hidden(sK0,k2_zfmisc_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))))),
% 0.20/0.43    inference(definition_unfolding,[],[f21,f24,f24])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => (~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.43    inference(flattening,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & (r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 0.20/0.43    inference(negated_conjecture,[],[f9])).
% 0.20/0.43  fof(f9,conjecture,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl5_6 | ~spl5_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f64,f44,f71])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl5_2 <=> r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    r1_tarski(k2_tarski(sK0,sK0),k2_zfmisc_1(sK3,sK4)) | ~spl5_2),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f46,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f27,f22])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) | ~spl5_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f44])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl5_3 | ~spl5_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f48,f39,f51])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl5_1 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK0,X0),k2_zfmisc_1(sK1,sK2))) ) | ~spl5_1),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f41,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl5_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl5_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f44])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl5_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f19,f39])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (4377)------------------------------
% 0.20/0.43  % (4377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (4377)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (4377)Memory used [KB]: 10618
% 0.20/0.43  % (4377)Time elapsed: 0.006 s
% 0.20/0.43  % (4377)------------------------------
% 0.20/0.43  % (4377)------------------------------
% 0.20/0.43  % (4359)Success in time 0.071 s
%------------------------------------------------------------------------------
