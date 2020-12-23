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
% DateTime   : Thu Dec  3 12:49:51 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 123 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  185 ( 546 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1125,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f33,f345,f1114])).

fof(f1114,plain,(
    ! [X12,X13] :
      ( sP1(X12,X13,X12)
      | ~ r1_tarski(X13,X12) ) ),
    inference(subsumption_resolution,[],[f1113,f236])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X0),X2)
      | sP1(X0,X1,X0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f231,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f231,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,X0),X1)
      | sP1(X0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f227,f118])).

fof(f118,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK6(X6,X7,X8),X8)
      | sP1(X6,X7,X8)
      | ~ r2_hidden(sK6(X6,X7,X8),X6) ) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,sK6(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f227,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,X0),X0)
      | sP1(X0,X1,X0)
      | r2_hidden(sK6(X0,X1,X0),X1) ) ),
    inference(factoring,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP1(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f46,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK6(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1113,plain,(
    ! [X12,X13] :
      ( sP1(X12,X13,X12)
      | ~ r1_tarski(X13,X12)
      | ~ r2_hidden(sK6(X12,X13,X12),X12) ) ),
    inference(duplicate_literal_removal,[],[f1110])).

fof(f1110,plain,(
    ! [X12,X13] :
      ( sP1(X12,X13,X12)
      | ~ r1_tarski(X13,X12)
      | sP1(X12,X13,X12)
      | ~ r2_hidden(sK6(X12,X13,X12),X12) ) ),
    inference(resolution,[],[f236,f118])).

fof(f345,plain,(
    ! [X0] : ~ sP1(X0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f343,f32])).

fof(f32,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f343,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK4)
      | ~ sP1(X0,sK2,sK3) ) ),
    inference(resolution,[],[f157,f34])).

fof(f34,plain,(
    ~ r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X3,X0),k9_relat_1(X3,X2))
      | ~ v1_relat_1(X3)
      | ~ sP1(X1,X0,X2) ) ),
    inference(superposition,[],[f93,f72])).

fof(f72,plain,(
    ! [X6,X4,X5] :
      ( k2_xboole_0(X5,X4) = X6
      | ~ sP1(X4,X5,X6) ) ),
    inference(superposition,[],[f52,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f3,f14,f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k2_xboole_0(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f33,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:20:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (623)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (599)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (598)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (612)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (611)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (602)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (621)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (603)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (613)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.54  % (607)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.54  % (615)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.54  % (615)Refutation not found, incomplete strategy% (615)------------------------------
% 1.33/0.54  % (615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (600)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (615)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (615)Memory used [KB]: 10618
% 1.33/0.54  % (615)Time elapsed: 0.127 s
% 1.33/0.54  % (615)------------------------------
% 1.33/0.54  % (615)------------------------------
% 1.33/0.54  % (614)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.54  % (619)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.54  % (605)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.54  % (610)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  % (604)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.55  % (608)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.55  % (606)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.55  % (616)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.55  % (618)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.46/0.56  % (620)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.46/0.56  % (626)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.56  % (620)Refutation not found, incomplete strategy% (620)------------------------------
% 1.46/0.56  % (620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (622)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.46/0.56  % (627)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.56  % (624)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.46/0.57  % (625)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.57  % (601)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.46/0.58  % (620)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (620)Memory used [KB]: 10746
% 1.46/0.58  % (620)Time elapsed: 0.153 s
% 1.46/0.58  % (620)------------------------------
% 1.46/0.58  % (620)------------------------------
% 1.46/0.58  % (609)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.58  % (617)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.38/0.68  % (627)Refutation found. Thanks to Tanya!
% 2.38/0.68  % SZS status Theorem for theBenchmark
% 2.38/0.68  % SZS output start Proof for theBenchmark
% 2.38/0.68  fof(f1125,plain,(
% 2.38/0.68    $false),
% 2.38/0.68    inference(unit_resulting_resolution,[],[f33,f345,f1114])).
% 2.38/0.68  fof(f1114,plain,(
% 2.38/0.68    ( ! [X12,X13] : (sP1(X12,X13,X12) | ~r1_tarski(X13,X12)) )),
% 2.38/0.68    inference(subsumption_resolution,[],[f1113,f236])).
% 2.38/0.68  fof(f236,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X0),X2) | sP1(X0,X1,X0) | ~r1_tarski(X1,X2)) )),
% 2.38/0.68    inference(resolution,[],[f231,f40])).
% 2.38/0.68  fof(f40,plain,(
% 2.38/0.68    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f23])).
% 2.38/0.68  fof(f23,plain,(
% 2.38/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).
% 2.38/0.68  fof(f22,plain,(
% 2.38/0.68    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f21,plain,(
% 2.38/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.68    inference(rectify,[],[f20])).
% 2.38/0.68  fof(f20,plain,(
% 2.38/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/0.68    inference(nnf_transformation,[],[f11])).
% 2.38/0.68  fof(f11,plain,(
% 2.38/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.38/0.68    inference(ennf_transformation,[],[f2])).
% 2.38/0.68  fof(f2,axiom,(
% 2.38/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.38/0.68  fof(f231,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,X0),X1) | sP1(X0,X1,X0)) )),
% 2.38/0.68    inference(subsumption_resolution,[],[f227,f118])).
% 2.38/0.68  fof(f118,plain,(
% 2.38/0.68    ( ! [X6,X8,X7] : (~r2_hidden(sK6(X6,X7,X8),X8) | sP1(X6,X7,X8) | ~r2_hidden(sK6(X6,X7,X8),X6)) )),
% 2.38/0.68    inference(resolution,[],[f47,f49])).
% 2.38/0.68  fof(f49,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X2)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f30])).
% 2.38/0.68  fof(f30,plain,(
% 2.38/0.68    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP0(X0,X1,X2)))),
% 2.38/0.68    inference(rectify,[],[f29])).
% 2.38/0.68  fof(f29,plain,(
% 2.38/0.68    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP0(X1,X3,X0)))),
% 2.38/0.68    inference(flattening,[],[f28])).
% 2.38/0.68  fof(f28,plain,(
% 2.38/0.68    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 2.38/0.68    inference(nnf_transformation,[],[f13])).
% 2.38/0.68  fof(f13,plain,(
% 2.38/0.68    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 2.38/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.38/0.68  fof(f47,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (~sP0(X1,sK6(X0,X1,X2),X0) | sP1(X0,X1,X2) | ~r2_hidden(sK6(X0,X1,X2),X2)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f27])).
% 2.38/0.68  fof(f27,plain,(
% 2.38/0.68    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).
% 2.38/0.68  fof(f26,plain,(
% 2.38/0.68    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f25,plain,(
% 2.38/0.68    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 2.38/0.68    inference(rectify,[],[f24])).
% 2.38/0.68  fof(f24,plain,(
% 2.38/0.68    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 2.38/0.68    inference(nnf_transformation,[],[f14])).
% 2.38/0.68  fof(f14,plain,(
% 2.38/0.68    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 2.38/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.38/0.68  fof(f227,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,X0),X0) | sP1(X0,X1,X0) | r2_hidden(sK6(X0,X1,X0),X1)) )),
% 2.38/0.68    inference(factoring,[],[f102])).
% 2.38/0.68  fof(f102,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | sP1(X0,X1,X2) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X1)) )),
% 2.38/0.68    inference(resolution,[],[f46,f48])).
% 2.38/0.68  fof(f48,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2) | r2_hidden(X1,X0)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f30])).
% 2.38/0.68  fof(f46,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (sP0(X1,sK6(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f27])).
% 2.38/0.68  fof(f1113,plain,(
% 2.38/0.68    ( ! [X12,X13] : (sP1(X12,X13,X12) | ~r1_tarski(X13,X12) | ~r2_hidden(sK6(X12,X13,X12),X12)) )),
% 2.38/0.68    inference(duplicate_literal_removal,[],[f1110])).
% 2.38/0.68  fof(f1110,plain,(
% 2.38/0.68    ( ! [X12,X13] : (sP1(X12,X13,X12) | ~r1_tarski(X13,X12) | sP1(X12,X13,X12) | ~r2_hidden(sK6(X12,X13,X12),X12)) )),
% 2.38/0.68    inference(resolution,[],[f236,f118])).
% 2.38/0.68  fof(f345,plain,(
% 2.38/0.68    ( ! [X0] : (~sP1(X0,sK2,sK3)) )),
% 2.38/0.68    inference(subsumption_resolution,[],[f343,f32])).
% 2.38/0.68  fof(f32,plain,(
% 2.38/0.68    v1_relat_1(sK4)),
% 2.38/0.68    inference(cnf_transformation,[],[f17])).
% 2.38/0.68  fof(f17,plain,(
% 2.38/0.68    ~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4)),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f16])).
% 2.38/0.68  fof(f16,plain,(
% 2.38/0.68    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK4))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f10,plain,(
% 2.38/0.68    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 2.38/0.68    inference(flattening,[],[f9])).
% 2.38/0.68  fof(f9,plain,(
% 2.38/0.68    ? [X0,X1,X2] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 2.38/0.68    inference(ennf_transformation,[],[f8])).
% 2.38/0.68  fof(f8,negated_conjecture,(
% 2.38/0.68    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.38/0.68    inference(negated_conjecture,[],[f7])).
% 2.38/0.68  fof(f7,conjecture,(
% 2.38/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 2.38/0.68  fof(f343,plain,(
% 2.38/0.68    ( ! [X0] : (~v1_relat_1(sK4) | ~sP1(X0,sK2,sK3)) )),
% 2.38/0.68    inference(resolution,[],[f157,f34])).
% 2.38/0.68  fof(f34,plain,(
% 2.38/0.68    ~r1_tarski(k9_relat_1(sK4,sK2),k9_relat_1(sK4,sK3))),
% 2.38/0.68    inference(cnf_transformation,[],[f17])).
% 2.38/0.68  fof(f157,plain,(
% 2.38/0.68    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X3,X0),k9_relat_1(X3,X2)) | ~v1_relat_1(X3) | ~sP1(X1,X0,X2)) )),
% 2.38/0.68    inference(superposition,[],[f93,f72])).
% 2.38/0.68  fof(f72,plain,(
% 2.38/0.68    ( ! [X6,X4,X5] : (k2_xboole_0(X5,X4) = X6 | ~sP1(X4,X5,X6)) )),
% 2.38/0.68    inference(superposition,[],[f52,f36])).
% 2.38/0.68  fof(f36,plain,(
% 2.38/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f1])).
% 2.38/0.68  fof(f1,axiom,(
% 2.38/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.38/0.68  fof(f52,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f31])).
% 2.38/0.68  fof(f31,plain,(
% 2.38/0.68    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 2.38/0.68    inference(nnf_transformation,[],[f15])).
% 2.38/0.68  fof(f15,plain,(
% 2.38/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 2.38/0.68    inference(definition_folding,[],[f3,f14,f13])).
% 2.38/0.68  fof(f3,axiom,(
% 2.38/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.38/0.68  fof(f93,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k2_xboole_0(X1,X2))) | ~v1_relat_1(X0)) )),
% 2.38/0.68    inference(superposition,[],[f35,f43])).
% 2.38/0.68  fof(f43,plain,(
% 2.38/0.68    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f12])).
% 2.38/0.68  fof(f12,plain,(
% 2.38/0.68    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.38/0.68    inference(ennf_transformation,[],[f6])).
% 2.38/0.68  fof(f6,axiom,(
% 2.38/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
% 2.38/0.68  fof(f35,plain,(
% 2.38/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.38/0.68    inference(cnf_transformation,[],[f5])).
% 2.38/0.68  fof(f5,axiom,(
% 2.38/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.38/0.68  fof(f33,plain,(
% 2.38/0.68    r1_tarski(sK2,sK3)),
% 2.38/0.68    inference(cnf_transformation,[],[f17])).
% 2.38/0.68  % SZS output end Proof for theBenchmark
% 2.38/0.68  % (627)------------------------------
% 2.38/0.68  % (627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.68  % (627)Termination reason: Refutation
% 2.38/0.68  
% 2.38/0.68  % (627)Memory used [KB]: 2302
% 2.38/0.68  % (627)Time elapsed: 0.261 s
% 2.38/0.68  % (627)------------------------------
% 2.38/0.68  % (627)------------------------------
% 2.38/0.68  % (597)Success in time 0.316 s
%------------------------------------------------------------------------------
