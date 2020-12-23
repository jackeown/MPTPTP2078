%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:34 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 245 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  266 ( 509 expanded)
%              Number of equality atoms :  125 ( 252 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f513,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f162,f165,f242,f490])).

% (14180)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f490,plain,
    ( ~ spl1_1
    | spl1_2
    | ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl1_1
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f488,f92])).

fof(f92,plain,
    ( o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl1_2
  <=> o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f488,plain,
    ( o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f487,f87])).

fof(f87,plain,
    ( o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl1_1
  <=> o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f487,plain,
    ( k2_relat_1(o_0_0_xboole_0) = k1_relat_1(o_0_0_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f473,f157])).

fof(f157,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl1_3
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f473,plain,
    ( k2_relat_1(o_0_0_xboole_0) = k1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(superposition,[],[f49,f467])).

fof(f467,plain,
    ( o_0_0_xboole_0 = k4_relat_1(o_0_0_xboole_0)
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f466,f67])).

fof(f67,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_setfam_1(k2_tarski(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f41,f40,f55,f40])).

fof(f55,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f466,plain,
    ( k4_relat_1(o_0_0_xboole_0) = k1_setfam_1(k2_tarski(k4_relat_1(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(forward_demodulation,[],[f465,f80])).

fof(f80,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f58,f40,f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

% (14187)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f465,plain,
    ( k4_relat_1(o_0_0_xboole_0) = k1_setfam_1(k2_tarski(k4_relat_1(o_0_0_xboole_0),k2_zfmisc_1(k2_relat_1(o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl1_1
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f459,f157])).

fof(f459,plain,
    ( k4_relat_1(o_0_0_xboole_0) = k1_setfam_1(k2_tarski(k4_relat_1(o_0_0_xboole_0),k2_zfmisc_1(k2_relat_1(o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl1_1 ),
    inference(superposition,[],[f452,f87])).

fof(f452,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k1_setfam_1(k2_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f451])).

fof(f451,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k1_setfam_1(k2_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f126,f49])).

% (14184)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f126,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k1_setfam_1(k2_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0)))))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f124,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f124,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k1_setfam_1(k2_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0)))))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f70,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f70,plain,(
    ! [X0] :
      ( k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f47,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f49,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f242,plain,
    ( spl1_1
    | ~ spl1_4 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl1_1
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f214,f186])).

fof(f186,plain,
    ( ! [X0] : sK0(k1_relat_1(o_0_0_xboole_0)) = X0
    | spl1_1
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f185,f88])).

fof(f88,plain,
    ( o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f185,plain,
    ( ! [X0] :
        ( sK0(k1_relat_1(o_0_0_xboole_0)) = X0
        | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) )
    | ~ spl1_4 ),
    inference(resolution,[],[f184,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f40])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f32])).

% (14180)Refutation not found, incomplete strategy% (14180)------------------------------
% (14180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14180)Termination reason: Refutation not found, incomplete strategy

% (14180)Memory used [KB]: 1663
% (14180)Time elapsed: 0.153 s
% (14180)------------------------------
% (14180)------------------------------
fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(o_0_0_xboole_0))
        | X0 = X1 )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f181,f109])).

fof(f109,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(superposition,[],[f82,f68])).

fof(f68,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f42,f40,f40])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f82,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) ) ),
    inference(definition_unfolding,[],[f60,f44])).

% (14161)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f181,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,o_0_0_xboole_0)
        | X0 = X1
        | ~ r2_hidden(X1,k1_relat_1(o_0_0_xboole_0)) )
    | ~ spl1_4 ),
    inference(superposition,[],[f77,f179])).

fof(f179,plain,
    ( ! [X3,X1] : o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_tarski(X1,X3))
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f177,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f177,plain,
    ( ! [X2,X0,X3,X1] :
        ( o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_tarski(X1,X3))
        | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) )
    | ~ spl1_4 ),
    inference(superposition,[],[f167,f176])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f83,f62])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X4) = k2_tarski(X1,X3)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f167,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f166,f46])).

fof(f166,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_relat_1(X0))
        | ~ v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(superposition,[],[f161,f48])).

fof(f161,plain,
    ( ! [X5] :
        ( o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k1_relat_1(X5))
        | ~ v1_relat_1(X5) )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f160])).

% (14168)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f160,plain,
    ( spl1_4
  <=> ! [X5] :
        ( o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k1_relat_1(X5))
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f44])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f214,plain,
    ( o_0_0_xboole_0 != sK0(k1_relat_1(o_0_0_xboole_0))
    | spl1_1
    | ~ spl1_4 ),
    inference(superposition,[],[f102,f186])).

fof(f102,plain,(
    ! [X0] : o_0_0_xboole_0 != k2_tarski(X0,X0) ),
    inference(superposition,[],[f72,f69])).

fof(f69,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

% (14182)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (14168)Refutation not found, incomplete strategy% (14168)------------------------------
% (14168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14160)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (14160)Refutation not found, incomplete strategy% (14160)------------------------------
% (14160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14179)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (14162)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (14177)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (14168)Termination reason: Refutation not found, incomplete strategy

% (14168)Memory used [KB]: 10618
% (14168)Time elapsed: 0.154 s
% (14168)------------------------------
% (14168)------------------------------
fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f72,plain,(
    ! [X0,X1] : o_0_0_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(definition_unfolding,[],[f52,f40,f44])).

fof(f52,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f165,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f163,f66])).

fof(f66,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f163,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f158,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f158,plain,
    ( ~ v1_relat_1(o_0_0_xboole_0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f162,plain,
    ( ~ spl1_3
    | spl1_4 ),
    inference(avatar_split_clause,[],[f152,f160,f156])).

fof(f152,plain,(
    ! [X5] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k1_relat_1(X5))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(o_0_0_xboole_0) ) ),
    inference(superposition,[],[f143,f94])).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[],[f54,f69])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f143,plain,(
    ! [X2,X3] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(X2),k1_relat_1(k2_xboole_0(X2,X3)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f73,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f53,f40])).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f93,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f65,f90,f86])).

fof(f65,plain,
    ( o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f38,f40,f40,f40,f40])).

fof(f38,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:59:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (14186)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.54  % (14166)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.54  % (14164)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.54  % (14158)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (14166)Refutation not found, incomplete strategy% (14166)------------------------------
% 1.37/0.54  % (14166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (14166)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (14166)Memory used [KB]: 10618
% 1.37/0.54  % (14166)Time elapsed: 0.113 s
% 1.37/0.54  % (14166)------------------------------
% 1.37/0.54  % (14166)------------------------------
% 1.37/0.54  % (14163)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.54  % (14158)Refutation not found, incomplete strategy% (14158)------------------------------
% 1.37/0.54  % (14158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (14158)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (14158)Memory used [KB]: 1663
% 1.37/0.54  % (14158)Time elapsed: 0.130 s
% 1.37/0.54  % (14158)------------------------------
% 1.37/0.54  % (14158)------------------------------
% 1.37/0.55  % (14183)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.55  % (14174)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.55  % (14181)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.55  % (14167)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.55  % (14181)Refutation not found, incomplete strategy% (14181)------------------------------
% 1.37/0.55  % (14181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (14181)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (14181)Memory used [KB]: 10618
% 1.37/0.55  % (14181)Time elapsed: 0.136 s
% 1.37/0.55  % (14181)------------------------------
% 1.37/0.55  % (14181)------------------------------
% 1.37/0.55  % (14173)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.55  % (14186)Refutation found. Thanks to Tanya!
% 1.37/0.55  % SZS status Theorem for theBenchmark
% 1.37/0.55  % (14172)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.56  % (14165)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.51/0.56  % (14176)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.56  % (14176)Refutation not found, incomplete strategy% (14176)------------------------------
% 1.51/0.56  % (14176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (14176)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (14176)Memory used [KB]: 10618
% 1.51/0.56  % (14176)Time elapsed: 0.101 s
% 1.51/0.56  % (14176)------------------------------
% 1.51/0.56  % (14176)------------------------------
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f513,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(avatar_sat_refutation,[],[f93,f162,f165,f242,f490])).
% 1.51/0.56  % (14180)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.56  fof(f490,plain,(
% 1.51/0.56    ~spl1_1 | spl1_2 | ~spl1_3),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f489])).
% 1.51/0.56  fof(f489,plain,(
% 1.51/0.56    $false | (~spl1_1 | spl1_2 | ~spl1_3)),
% 1.51/0.56    inference(subsumption_resolution,[],[f488,f92])).
% 1.51/0.56  fof(f92,plain,(
% 1.51/0.56    o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0) | spl1_2),
% 1.51/0.56    inference(avatar_component_clause,[],[f90])).
% 1.51/0.56  fof(f90,plain,(
% 1.51/0.56    spl1_2 <=> o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.51/0.56  fof(f488,plain,(
% 1.51/0.56    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) | (~spl1_1 | ~spl1_3)),
% 1.51/0.56    inference(forward_demodulation,[],[f487,f87])).
% 1.51/0.56  fof(f87,plain,(
% 1.51/0.56    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) | ~spl1_1),
% 1.51/0.56    inference(avatar_component_clause,[],[f86])).
% 1.51/0.56  fof(f86,plain,(
% 1.51/0.56    spl1_1 <=> o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.51/0.56  fof(f487,plain,(
% 1.51/0.56    k2_relat_1(o_0_0_xboole_0) = k1_relat_1(o_0_0_xboole_0) | (~spl1_1 | ~spl1_3)),
% 1.51/0.56    inference(subsumption_resolution,[],[f473,f157])).
% 1.51/0.56  fof(f157,plain,(
% 1.51/0.56    v1_relat_1(o_0_0_xboole_0) | ~spl1_3),
% 1.51/0.56    inference(avatar_component_clause,[],[f156])).
% 1.51/0.56  fof(f156,plain,(
% 1.51/0.56    spl1_3 <=> v1_relat_1(o_0_0_xboole_0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.51/0.56  fof(f473,plain,(
% 1.51/0.56    k2_relat_1(o_0_0_xboole_0) = k1_relat_1(o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | (~spl1_1 | ~spl1_3)),
% 1.51/0.56    inference(superposition,[],[f49,f467])).
% 1.51/0.56  fof(f467,plain,(
% 1.51/0.56    o_0_0_xboole_0 = k4_relat_1(o_0_0_xboole_0) | (~spl1_1 | ~spl1_3)),
% 1.51/0.56    inference(forward_demodulation,[],[f466,f67])).
% 1.51/0.56  fof(f67,plain,(
% 1.51/0.56    ( ! [X0] : (o_0_0_xboole_0 = k1_setfam_1(k2_tarski(X0,o_0_0_xboole_0))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f41,f40,f55,f40])).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,axiom,(
% 1.51/0.56    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    k1_xboole_0 = o_0_0_xboole_0),
% 1.51/0.56    inference(cnf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    k1_xboole_0 = o_0_0_xboole_0),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.51/0.56  fof(f466,plain,(
% 1.51/0.56    k4_relat_1(o_0_0_xboole_0) = k1_setfam_1(k2_tarski(k4_relat_1(o_0_0_xboole_0),o_0_0_xboole_0)) | (~spl1_1 | ~spl1_3)),
% 1.51/0.56    inference(forward_demodulation,[],[f465,f80])).
% 1.51/0.56  fof(f80,plain,(
% 1.51/0.56    ( ! [X0] : (o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0)) )),
% 1.51/0.56    inference(equality_resolution,[],[f74])).
% 1.51/0.56  fof(f74,plain,(
% 1.51/0.56    ( ! [X0,X1] : (o_0_0_xboole_0 = k2_zfmisc_1(X0,X1) | o_0_0_xboole_0 != X1) )),
% 1.51/0.56    inference(definition_unfolding,[],[f58,f40,f40])).
% 1.51/0.56  fof(f58,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f35])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.51/0.56    inference(flattening,[],[f34])).
% 1.51/0.56  % (14187)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.51/0.56    inference(nnf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.51/0.56  fof(f465,plain,(
% 1.51/0.56    k4_relat_1(o_0_0_xboole_0) = k1_setfam_1(k2_tarski(k4_relat_1(o_0_0_xboole_0),k2_zfmisc_1(k2_relat_1(o_0_0_xboole_0),o_0_0_xboole_0))) | (~spl1_1 | ~spl1_3)),
% 1.51/0.56    inference(subsumption_resolution,[],[f459,f157])).
% 1.51/0.56  fof(f459,plain,(
% 1.51/0.56    k4_relat_1(o_0_0_xboole_0) = k1_setfam_1(k2_tarski(k4_relat_1(o_0_0_xboole_0),k2_zfmisc_1(k2_relat_1(o_0_0_xboole_0),o_0_0_xboole_0))) | ~v1_relat_1(o_0_0_xboole_0) | ~spl1_1),
% 1.51/0.56    inference(superposition,[],[f452,f87])).
% 1.51/0.56  fof(f452,plain,(
% 1.51/0.56    ( ! [X0] : (k4_relat_1(X0) = k1_setfam_1(k2_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f451])).
% 1.51/0.56  fof(f451,plain,(
% 1.51/0.56    ( ! [X0] : (k4_relat_1(X0) = k1_setfam_1(k2_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k1_relat_1(X0)))) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.56    inference(superposition,[],[f126,f49])).
% 1.51/0.56  % (14184)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.56  fof(f126,plain,(
% 1.51/0.56    ( ! [X0] : (k4_relat_1(X0) = k1_setfam_1(k2_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0))))) | ~v1_relat_1(X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f124,f46])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f15])).
% 1.51/0.56  fof(f15,axiom,(
% 1.51/0.56    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.51/0.56  fof(f124,plain,(
% 1.51/0.56    ( ! [X0] : (k4_relat_1(X0) = k1_setfam_1(k2_tarski(k4_relat_1(X0),k2_zfmisc_1(k2_relat_1(X0),k2_relat_1(k4_relat_1(X0))))) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.51/0.56    inference(superposition,[],[f70,f48])).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f27])).
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f20])).
% 1.51/0.57  fof(f20,axiom,(
% 1.51/0.57    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.51/0.57  fof(f70,plain,(
% 1.51/0.57    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f47,f55])).
% 1.51/0.57  fof(f47,plain,(
% 1.51/0.57    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f26])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f18])).
% 1.51/0.57  fof(f18,axiom,(
% 1.51/0.57    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.51/0.57  fof(f49,plain,(
% 1.51/0.57    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f27])).
% 1.51/0.57  fof(f242,plain,(
% 1.51/0.57    spl1_1 | ~spl1_4),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f241])).
% 1.51/0.57  fof(f241,plain,(
% 1.51/0.57    $false | (spl1_1 | ~spl1_4)),
% 1.51/0.57    inference(subsumption_resolution,[],[f214,f186])).
% 1.51/0.57  fof(f186,plain,(
% 1.51/0.57    ( ! [X0] : (sK0(k1_relat_1(o_0_0_xboole_0)) = X0) ) | (spl1_1 | ~spl1_4)),
% 1.51/0.57    inference(subsumption_resolution,[],[f185,f88])).
% 1.51/0.57  fof(f88,plain,(
% 1.51/0.57    o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0) | spl1_1),
% 1.51/0.57    inference(avatar_component_clause,[],[f86])).
% 1.51/0.57  fof(f185,plain,(
% 1.51/0.57    ( ! [X0] : (sK0(k1_relat_1(o_0_0_xboole_0)) = X0 | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)) ) | ~spl1_4),
% 1.51/0.57    inference(resolution,[],[f184,f71])).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ( ! [X0] : (r2_hidden(sK0(X0),X0) | o_0_0_xboole_0 = X0) )),
% 1.51/0.57    inference(definition_unfolding,[],[f51,f40])).
% 1.51/0.57  fof(f51,plain,(
% 1.51/0.57    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f33])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f32])).
% 1.51/0.57  % (14180)Refutation not found, incomplete strategy% (14180)------------------------------
% 1.51/0.57  % (14180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (14180)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (14180)Memory used [KB]: 1663
% 1.51/0.57  % (14180)Time elapsed: 0.153 s
% 1.51/0.57  % (14180)------------------------------
% 1.51/0.57  % (14180)------------------------------
% 1.51/0.57  fof(f32,plain,(
% 1.51/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f29,plain,(
% 1.51/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.51/0.57    inference(ennf_transformation,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.51/0.57  fof(f184,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(o_0_0_xboole_0)) | X0 = X1) ) | ~spl1_4),
% 1.51/0.57    inference(subsumption_resolution,[],[f181,f109])).
% 1.51/0.57  fof(f109,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) )),
% 1.51/0.57    inference(superposition,[],[f82,f68])).
% 1.51/0.57  fof(f68,plain,(
% 1.51/0.57    ( ! [X0] : (o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f42,f40,f40])).
% 1.51/0.57  fof(f42,plain,(
% 1.51/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,axiom,(
% 1.51/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.51/0.57  fof(f82,plain,(
% 1.51/0.57    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 1.51/0.57    inference(equality_resolution,[],[f78])).
% 1.51/0.57  fof(f78,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f60,f44])).
% 1.51/0.57  % (14161)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.57  fof(f44,plain,(
% 1.51/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f9])).
% 1.51/0.57  fof(f9,axiom,(
% 1.51/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.51/0.57  fof(f60,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.51/0.57    inference(flattening,[],[f36])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.51/0.57    inference(nnf_transformation,[],[f12])).
% 1.51/0.57  fof(f12,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.51/0.57  fof(f181,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r2_hidden(X1,o_0_0_xboole_0) | X0 = X1 | ~r2_hidden(X1,k1_relat_1(o_0_0_xboole_0))) ) | ~spl1_4),
% 1.51/0.57    inference(superposition,[],[f77,f179])).
% 1.51/0.57  fof(f179,plain,(
% 1.51/0.57    ( ! [X3,X1] : (o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_tarski(X1,X3))) ) | ~spl1_4),
% 1.51/0.57    inference(subsumption_resolution,[],[f177,f62])).
% 1.51/0.57  fof(f62,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f16])).
% 1.51/0.57  fof(f16,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 1.51/0.57  fof(f177,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_tarski(X1,X3)) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) ) | ~spl1_4),
% 1.51/0.57    inference(superposition,[],[f167,f176])).
% 1.51/0.57  fof(f176,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f83,f62])).
% 1.51/0.57  fof(f83,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.51/0.57    inference(equality_resolution,[],[f64])).
% 1.51/0.57  fof(f64,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X4) = k2_tarski(X1,X3) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f31])).
% 1.51/0.57  fof(f31,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 1.51/0.57    inference(flattening,[],[f30])).
% 1.51/0.57  fof(f30,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 1.51/0.57    inference(ennf_transformation,[],[f19])).
% 1.51/0.57  fof(f19,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).
% 1.51/0.57  fof(f167,plain,(
% 1.51/0.57    ( ! [X0] : (o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.51/0.57    inference(subsumption_resolution,[],[f166,f46])).
% 1.51/0.57  fof(f166,plain,(
% 1.51/0.57    ( ! [X0] : (o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k2_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 1.51/0.57    inference(superposition,[],[f161,f48])).
% 1.51/0.57  fof(f161,plain,(
% 1.51/0.57    ( ! [X5] : (o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k1_relat_1(X5)) | ~v1_relat_1(X5)) ) | ~spl1_4),
% 1.51/0.57    inference(avatar_component_clause,[],[f160])).
% 1.51/0.57  % (14168)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.57  fof(f160,plain,(
% 1.51/0.57    spl1_4 <=> ! [X5] : (o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k1_relat_1(X5)) | ~v1_relat_1(X5))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.51/0.57  fof(f77,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f61,f44])).
% 1.51/0.57  fof(f61,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f214,plain,(
% 1.51/0.57    o_0_0_xboole_0 != sK0(k1_relat_1(o_0_0_xboole_0)) | (spl1_1 | ~spl1_4)),
% 1.51/0.57    inference(superposition,[],[f102,f186])).
% 1.51/0.57  fof(f102,plain,(
% 1.51/0.57    ( ! [X0] : (o_0_0_xboole_0 != k2_tarski(X0,X0)) )),
% 1.51/0.57    inference(superposition,[],[f72,f69])).
% 1.51/0.57  fof(f69,plain,(
% 1.51/0.57    ( ! [X0] : (k2_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 1.51/0.57    inference(definition_unfolding,[],[f43,f40])).
% 1.51/0.57  fof(f43,plain,(
% 1.51/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f5])).
% 1.51/0.57  % (14182)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.57  % (14168)Refutation not found, incomplete strategy% (14168)------------------------------
% 1.51/0.57  % (14168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (14160)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.51/0.57  % (14160)Refutation not found, incomplete strategy% (14160)------------------------------
% 1.51/0.57  % (14160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (14179)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.57  % (14162)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.51/0.57  % (14177)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.57  % (14168)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (14168)Memory used [KB]: 10618
% 1.51/0.57  % (14168)Time elapsed: 0.154 s
% 1.51/0.57  % (14168)------------------------------
% 1.51/0.57  % (14168)------------------------------
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.51/0.57  fof(f72,plain,(
% 1.51/0.57    ( ! [X0,X1] : (o_0_0_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f52,f40,f44])).
% 1.51/0.57  fof(f52,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f11])).
% 1.51/0.57  fof(f11,axiom,(
% 1.51/0.57    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.51/0.57  fof(f165,plain,(
% 1.51/0.57    spl1_3),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f164])).
% 1.51/0.57  fof(f164,plain,(
% 1.51/0.57    $false | spl1_3),
% 1.51/0.57    inference(subsumption_resolution,[],[f163,f66])).
% 1.51/0.57  fof(f66,plain,(
% 1.51/0.57    v1_xboole_0(o_0_0_xboole_0)),
% 1.51/0.57    inference(definition_unfolding,[],[f39,f40])).
% 1.51/0.57  fof(f39,plain,(
% 1.51/0.57    v1_xboole_0(k1_xboole_0)),
% 1.51/0.57    inference(cnf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    v1_xboole_0(k1_xboole_0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.51/0.57  fof(f163,plain,(
% 1.51/0.57    ~v1_xboole_0(o_0_0_xboole_0) | spl1_3),
% 1.51/0.57    inference(resolution,[],[f158,f45])).
% 1.51/0.57  fof(f45,plain,(
% 1.51/0.57    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f24])).
% 1.51/0.57  fof(f24,plain,(
% 1.51/0.57    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f14])).
% 1.51/0.57  fof(f14,axiom,(
% 1.51/0.57    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.51/0.57  fof(f158,plain,(
% 1.51/0.57    ~v1_relat_1(o_0_0_xboole_0) | spl1_3),
% 1.51/0.57    inference(avatar_component_clause,[],[f156])).
% 1.51/0.57  fof(f162,plain,(
% 1.51/0.57    ~spl1_3 | spl1_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f152,f160,f156])).
% 1.51/0.57  fof(f152,plain,(
% 1.51/0.57    ( ! [X5] : (o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(o_0_0_xboole_0),k1_relat_1(X5)) | ~v1_relat_1(X5) | ~v1_relat_1(o_0_0_xboole_0)) )),
% 1.51/0.57    inference(superposition,[],[f143,f94])).
% 1.51/0.57  fof(f94,plain,(
% 1.51/0.57    ( ! [X0] : (k2_xboole_0(o_0_0_xboole_0,X0) = X0) )),
% 1.51/0.57    inference(superposition,[],[f54,f69])).
% 1.51/0.57  fof(f54,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f1])).
% 1.51/0.57  fof(f1,axiom,(
% 1.51/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.51/0.57  fof(f143,plain,(
% 1.51/0.57    ( ! [X2,X3] : (o_0_0_xboole_0 = k4_xboole_0(k1_relat_1(X2),k1_relat_1(k2_xboole_0(X2,X3))) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.51/0.57    inference(superposition,[],[f73,f50])).
% 1.51/0.57  fof(f50,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f28])).
% 1.51/0.57  fof(f28,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f17])).
% 1.51/0.57  fof(f17,axiom,(
% 1.51/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 1.51/0.57  fof(f73,plain,(
% 1.51/0.57    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f53,f40])).
% 1.51/0.57  fof(f53,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,axiom,(
% 1.51/0.57    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.51/0.57  fof(f93,plain,(
% 1.51/0.57    ~spl1_1 | ~spl1_2),
% 1.51/0.57    inference(avatar_split_clause,[],[f65,f90,f86])).
% 1.51/0.57  fof(f65,plain,(
% 1.51/0.57    o_0_0_xboole_0 != k2_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0)),
% 1.51/0.57    inference(definition_unfolding,[],[f38,f40,f40,f40,f40])).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.51/0.57    inference(cnf_transformation,[],[f23])).
% 1.51/0.57  fof(f23,plain,(
% 1.51/0.57    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.51/0.57    inference(ennf_transformation,[],[f22])).
% 1.51/0.57  fof(f22,negated_conjecture,(
% 1.51/0.57    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.51/0.57    inference(negated_conjecture,[],[f21])).
% 1.51/0.57  fof(f21,conjecture,(
% 1.51/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (14186)------------------------------
% 1.51/0.57  % (14186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (14186)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (14186)Memory used [KB]: 6524
% 1.51/0.57  % (14186)Time elapsed: 0.149 s
% 1.51/0.57  % (14186)------------------------------
% 1.51/0.57  % (14186)------------------------------
% 1.51/0.57  % (14167)Refutation not found, incomplete strategy% (14167)------------------------------
% 1.51/0.57  % (14167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (14170)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (14159)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.57  % (14157)Success in time 0.208 s
%------------------------------------------------------------------------------
