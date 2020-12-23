%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 ( 414 expanded)
%              Number of equality atoms :   44 ( 100 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f476,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f362,f381,f384,f475])).

fof(f475,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f473,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2)
   => k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_1)).

fof(f473,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(subsumption_resolution,[],[f472,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f472,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(trivial_inequality_removal,[],[f471])).

fof(f471,plain,
    ( k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(superposition,[],[f361,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f361,plain,
    ( k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k5_relat_1(k7_relat_1(sK0,sK2),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl3_5
  <=> k7_relat_1(k5_relat_1(sK0,sK1),sK2) = k5_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f384,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f382,f26])).

fof(f382,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_4 ),
    inference(resolution,[],[f357,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f357,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl3_4
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f381,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f379,f26])).

fof(f379,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f378,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f378,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_3 ),
    inference(superposition,[],[f353,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f353,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k9_relat_1(sK0,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl3_3
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k9_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f362,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f349,f359,f355,f351])).

fof(f349,plain,
    ( k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k5_relat_1(k7_relat_1(sK0,sK2),sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k9_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f325,f28])).

fof(f325,plain,
    ( k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k5_relat_1(k7_relat_1(sK0,sK2),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k9_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f30,f291])).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,X1) = k5_relat_1(X2,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X0) ) ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,X1) = k5_relat_1(X2,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f86,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X2) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f85,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X2) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X2) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f33,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f30,plain,(
    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (27072)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.47  % (27088)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (27068)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (27067)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (27073)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (27087)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (27086)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (27066)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (27069)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (27078)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (27082)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (27085)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (27064)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (27070)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (27083)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (27080)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (27065)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27077)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (27076)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (27075)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (27074)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (27071)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.55  % (27068)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f476,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f362,f381,f384,f475])).
% 0.21/0.55  fof(f475,plain,(
% 0.21/0.55    spl3_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f474])).
% 0.21/0.55  fof(f474,plain,(
% 0.21/0.55    $false | spl3_5),
% 0.21/0.55    inference(subsumption_resolution,[],[f473,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    v1_relat_1(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    (k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22,f21,f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(X1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X2] : k5_relat_1(k7_relat_1(sK0,X2),k7_relat_1(sK1,k9_relat_1(sK0,X2))) != k7_relat_1(k5_relat_1(sK0,sK1),X2) => k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) != k7_relat_1(k5_relat_1(X0,X1),X2) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2)))),
% 0.21/0.55    inference(negated_conjecture,[],[f9])).
% 0.21/0.55  fof(f9,conjecture,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : k5_relat_1(k7_relat_1(X0,X2),k7_relat_1(X1,k9_relat_1(X0,X2))) = k7_relat_1(k5_relat_1(X0,X1),X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_1)).
% 0.21/0.55  fof(f473,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | spl3_5),
% 0.21/0.55    inference(subsumption_resolution,[],[f472,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f472,plain,(
% 0.21/0.55    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_5),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f471])).
% 0.21/0.55  fof(f471,plain,(
% 0.21/0.55    k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k7_relat_1(k5_relat_1(sK0,sK1),sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_5),
% 0.21/0.55    inference(superposition,[],[f361,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 0.21/0.55  fof(f361,plain,(
% 0.21/0.55    k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k5_relat_1(k7_relat_1(sK0,sK2),sK1) | spl3_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f359])).
% 0.21/0.55  fof(f359,plain,(
% 0.21/0.55    spl3_5 <=> k7_relat_1(k5_relat_1(sK0,sK1),sK2) = k5_relat_1(k7_relat_1(sK0,sK2),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.55  fof(f384,plain,(
% 0.21/0.55    spl3_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f383])).
% 0.21/0.55  fof(f383,plain,(
% 0.21/0.55    $false | spl3_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f382,f26])).
% 0.21/0.55  fof(f382,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | spl3_4),
% 0.21/0.55    inference(resolution,[],[f357,f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.55  fof(f357,plain,(
% 0.21/0.55    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl3_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f355])).
% 0.21/0.55  fof(f355,plain,(
% 0.21/0.55    spl3_4 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.55  fof(f381,plain,(
% 0.21/0.55    spl3_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f380])).
% 0.21/0.55  fof(f380,plain,(
% 0.21/0.55    $false | spl3_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f379,f26])).
% 0.21/0.55  fof(f379,plain,(
% 0.21/0.55    ~v1_relat_1(sK0) | spl3_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f378,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  fof(f378,plain,(
% 0.21/0.55    ~r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_3),
% 0.21/0.55    inference(superposition,[],[f353,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.55  fof(f353,plain,(
% 0.21/0.55    ~r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k9_relat_1(sK0,sK2)) | spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f351])).
% 0.21/0.55  fof(f351,plain,(
% 0.21/0.55    spl3_3 <=> r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k9_relat_1(sK0,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f362,plain,(
% 0.21/0.55    ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f349,f359,f355,f351])).
% 0.21/0.55  fof(f349,plain,(
% 0.21/0.55    k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k5_relat_1(k7_relat_1(sK0,sK2),sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k9_relat_1(sK0,sK2))),
% 0.21/0.55    inference(subsumption_resolution,[],[f325,f28])).
% 0.21/0.55  fof(f325,plain,(
% 0.21/0.55    k7_relat_1(k5_relat_1(sK0,sK1),sK2) != k5_relat_1(k7_relat_1(sK0,sK2),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k9_relat_1(sK0,sK2))),
% 0.21/0.55    inference(superposition,[],[f30,f291])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_relat_1(X2,X1) = k5_relat_1(X2,k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f267])).
% 0.21/0.55  fof(f267,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_relat_1(X2,X1) = k5_relat_1(X2,k7_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(superposition,[],[f86,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_relat_1(X0,X2) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f85,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_relat_1(X0,X2) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_relat_1(X0,X2) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),X2)) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(superposition,[],[f33,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    k5_relat_1(k7_relat_1(sK0,sK2),k7_relat_1(sK1,k9_relat_1(sK0,sK2))) != k7_relat_1(k5_relat_1(sK0,sK1),sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (27068)------------------------------
% 0.21/0.55  % (27068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27068)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (27068)Memory used [KB]: 6524
% 0.21/0.55  % (27068)Time elapsed: 0.114 s
% 0.21/0.55  % (27068)------------------------------
% 0.21/0.55  % (27068)------------------------------
% 0.21/0.55  % (27089)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.56  % (27084)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (27081)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.56  % (27063)Success in time 0.205 s
%------------------------------------------------------------------------------
