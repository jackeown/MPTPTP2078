%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:26 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 319 expanded)
%              Number of leaves         :   13 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  163 ( 685 expanded)
%              Number of equality atoms :   38 ( 209 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1032,plain,(
    $false ),
    inference(global_subsumption,[],[f901,f1027])).

fof(f1027,plain,(
    r2_hidden(sK6(k2_relat_1(sK1),sK0),k4_xboole_0(sK0,k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f992,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ sP12(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP12(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f992,plain,(
    sP12(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f902,f943,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( sP12(X3,X1,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f943,plain,(
    ~ r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f933,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP8(X2,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP8(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f933,plain,(
    ~ sP8(sK6(k2_relat_1(sK1),sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f436,f902,f312])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK9(X2,X0),X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ sP8(X0,X2) ) ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK9(X0,X2),X2),X0)
      | ~ sP8(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f436,plain,(
    ! [X0] : ~ sP3(X0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f434,f311])).

fof(f311,plain,(
    ! [X0] :
      ( ~ sP3(X0,sK0,sK1)
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(global_subsumption,[],[f26,f76,f308])).

fof(f308,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP3(X0,sK0,sK1)
      | ~ v1_relat_1(sK1)
      | r1_xboole_0(k2_relat_1(sK1),sK0) ) ),
    inference(superposition,[],[f70,f24])).

fof(f24,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ sP3(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f27,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f434,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f433])).

fof(f433,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f427])).

fof(f427,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(superposition,[],[f25,f403])).

fof(f403,plain,(
    ! [X1] :
      ( k1_xboole_0 = k10_relat_1(sK1,X1)
      | ~ r1_xboole_0(k2_relat_1(sK1),X1) ) ),
    inference(forward_demodulation,[],[f397,f295])).

fof(f295,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f286,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f286,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f26,f136,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | sP3(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f136,plain,(
    ! [X0,X1] : ~ sP3(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f76,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X1)
      | ~ sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f397,plain,(
    ! [X1] :
      ( k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,X1)
      | ~ r1_xboole_0(k2_relat_1(sK1),X1) ) ),
    inference(superposition,[],[f381,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f381,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f26,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f25,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f902,plain,(
    r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f853,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ sP12(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f853,plain,(
    sP12(sK6(k2_relat_1(sK1),sK0),k4_xboole_0(sK0,k2_relat_1(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f443,f201])).

fof(f201,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_setfam_1(k2_tarski(X3,X4)))
      | sP12(X5,k4_xboole_0(X3,X4),X3) ) ),
    inference(superposition,[],[f73,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP12(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f443,plain,(
    r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f439,f62])).

fof(f62,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f37,f37])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f439,plain,(
    r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0))) ),
    inference(unit_resulting_resolution,[],[f434,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f901,plain,(
    ~ r2_hidden(sK6(k2_relat_1(sK1),sK0),k4_xboole_0(sK0,k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f853,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ sP12(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (12023)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (12007)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (12008)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (12009)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (12015)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (12011)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (12006)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (12026)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (12005)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (12015)Refutation not found, incomplete strategy% (12015)------------------------------
% 0.21/0.52  % (12015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12018)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (12015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12015)Memory used [KB]: 10746
% 0.21/0.52  % (12015)Time elapsed: 0.116 s
% 0.21/0.52  % (12015)------------------------------
% 0.21/0.52  % (12015)------------------------------
% 0.21/0.52  % (12016)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12010)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (12025)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (12014)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (12030)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (12012)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (12017)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (12024)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (12020)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (12004)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (12029)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (12032)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (12022)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (12028)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.54  % (12033)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.54  % (12026)Refutation not found, incomplete strategy% (12026)------------------------------
% 1.40/0.54  % (12026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (12026)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (12026)Memory used [KB]: 10746
% 1.40/0.54  % (12026)Time elapsed: 0.092 s
% 1.40/0.54  % (12026)------------------------------
% 1.40/0.54  % (12026)------------------------------
% 1.40/0.55  % (12027)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.55  % (12031)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (12013)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.55  % (12014)Refutation not found, incomplete strategy% (12014)------------------------------
% 1.40/0.55  % (12014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (12014)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (12014)Memory used [KB]: 10618
% 1.40/0.55  % (12014)Time elapsed: 0.125 s
% 1.40/0.55  % (12014)------------------------------
% 1.40/0.55  % (12014)------------------------------
% 1.40/0.55  % (12019)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (12021)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  % (12021)Refutation not found, incomplete strategy% (12021)------------------------------
% 1.40/0.55  % (12021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (12021)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (12021)Memory used [KB]: 10618
% 1.40/0.55  % (12021)Time elapsed: 0.149 s
% 1.40/0.55  % (12021)------------------------------
% 1.40/0.55  % (12021)------------------------------
% 1.55/0.60  % (12028)Refutation found. Thanks to Tanya!
% 1.55/0.60  % SZS status Theorem for theBenchmark
% 1.55/0.60  % SZS output start Proof for theBenchmark
% 1.55/0.60  fof(f1032,plain,(
% 1.55/0.60    $false),
% 1.55/0.60    inference(global_subsumption,[],[f901,f1027])).
% 1.55/0.60  fof(f1027,plain,(
% 1.55/0.60    r2_hidden(sK6(k2_relat_1(sK1),sK0),k4_xboole_0(sK0,k2_relat_1(sK1)))),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f992,f74])).
% 1.55/0.60  fof(f74,plain,(
% 1.55/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | ~sP12(X3,X1,X0)) )),
% 1.55/0.60    inference(equality_resolution,[],[f58])).
% 1.55/0.60  fof(f58,plain,(
% 1.55/0.60    ( ! [X2,X0,X3,X1] : (~sP12(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  fof(f2,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.55/0.60  fof(f992,plain,(
% 1.55/0.60    sP12(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1),sK0)),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f902,f943,f55])).
% 1.55/0.60  fof(f55,plain,(
% 1.55/0.60    ( ! [X0,X3,X1] : (sP12(X3,X1,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  fof(f943,plain,(
% 1.55/0.60    ~r2_hidden(sK6(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f933,f71])).
% 1.55/0.60  fof(f71,plain,(
% 1.55/0.60    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP8(X2,X0)) )),
% 1.55/0.60    inference(equality_resolution,[],[f47])).
% 1.55/0.60  fof(f47,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (sP8(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.55/0.60    inference(cnf_transformation,[],[f11])).
% 1.55/0.60  fof(f11,axiom,(
% 1.55/0.60    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.55/0.60  fof(f933,plain,(
% 1.55/0.60    ~sP8(sK6(k2_relat_1(sK1),sK0),sK1)),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f436,f902,f312])).
% 1.55/0.60  fof(f312,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (sP3(sK9(X2,X0),X1,X2) | ~r2_hidden(X0,X1) | ~sP8(X0,X2)) )),
% 1.55/0.60    inference(resolution,[],[f28,f44])).
% 1.55/0.60  fof(f44,plain,(
% 1.55/0.60    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK9(X0,X2),X2),X0) | ~sP8(X2,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f11])).
% 1.55/0.60  fof(f28,plain,(
% 1.55/0.60    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP3(X3,X1,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f18])).
% 1.55/0.60  fof(f18,plain,(
% 1.55/0.60    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.55/0.60    inference(ennf_transformation,[],[f10])).
% 1.55/0.60  fof(f10,axiom,(
% 1.55/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.55/0.60  fof(f436,plain,(
% 1.55/0.60    ( ! [X0] : (~sP3(X0,sK0,sK1)) )),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f434,f311])).
% 1.55/0.60  fof(f311,plain,(
% 1.55/0.60    ( ! [X0] : (~sP3(X0,sK0,sK1) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 1.55/0.60    inference(global_subsumption,[],[f26,f76,f308])).
% 1.55/0.60  fof(f308,plain,(
% 1.55/0.60    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP3(X0,sK0,sK1) | ~v1_relat_1(sK1) | r1_xboole_0(k2_relat_1(sK1),sK0)) )),
% 1.55/0.60    inference(superposition,[],[f70,f24])).
% 1.55/0.60  fof(f24,plain,(
% 1.55/0.60    k1_xboole_0 = k10_relat_1(sK1,sK0) | r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.55/0.60    inference(cnf_transformation,[],[f17])).
% 1.55/0.60  fof(f17,plain,(
% 1.55/0.60    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.55/0.60    inference(ennf_transformation,[],[f15])).
% 1.55/0.60  fof(f15,negated_conjecture,(
% 1.55/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.55/0.60    inference(negated_conjecture,[],[f14])).
% 1.55/0.60  fof(f14,conjecture,(
% 1.55/0.60    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.55/0.60  fof(f70,plain,(
% 1.55/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,k10_relat_1(X0,X1)) | ~sP3(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 1.55/0.60    inference(equality_resolution,[],[f31])).
% 1.55/0.60  fof(f31,plain,(
% 1.55/0.60    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.55/0.60    inference(cnf_transformation,[],[f18])).
% 1.55/0.60  fof(f76,plain,(
% 1.55/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f27,f50])).
% 1.55/0.60  fof(f50,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f22])).
% 1.55/0.60  fof(f22,plain,(
% 1.55/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.55/0.60    inference(ennf_transformation,[],[f8])).
% 1.55/0.60  fof(f8,axiom,(
% 1.55/0.60    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.55/0.60  fof(f27,plain,(
% 1.55/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f7])).
% 1.55/0.60  fof(f7,axiom,(
% 1.55/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.55/0.60  fof(f26,plain,(
% 1.55/0.60    v1_relat_1(sK1)),
% 1.55/0.60    inference(cnf_transformation,[],[f17])).
% 1.55/0.60  fof(f434,plain,(
% 1.55/0.60    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.55/0.60    inference(trivial_inequality_removal,[],[f433])).
% 1.55/0.60  fof(f433,plain,(
% 1.55/0.60    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.55/0.60    inference(duplicate_literal_removal,[],[f427])).
% 1.55/0.60  fof(f427,plain,(
% 1.55/0.60    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.55/0.60    inference(superposition,[],[f25,f403])).
% 1.55/0.60  fof(f403,plain,(
% 1.55/0.60    ( ! [X1] : (k1_xboole_0 = k10_relat_1(sK1,X1) | ~r1_xboole_0(k2_relat_1(sK1),X1)) )),
% 1.55/0.60    inference(forward_demodulation,[],[f397,f295])).
% 1.55/0.60  fof(f295,plain,(
% 1.55/0.60    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f286,f35])).
% 1.55/0.60  fof(f35,plain,(
% 1.55/0.60    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.55/0.60    inference(cnf_transformation,[],[f19])).
% 1.55/0.60  fof(f19,plain,(
% 1.55/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.55/0.60    inference(ennf_transformation,[],[f5])).
% 1.55/0.60  fof(f5,axiom,(
% 1.55/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.55/0.60  fof(f286,plain,(
% 1.55/0.60    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f26,f136,f69])).
% 1.55/0.60  fof(f69,plain,(
% 1.55/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | sP3(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 1.55/0.60    inference(equality_resolution,[],[f32])).
% 1.55/0.60  fof(f32,plain,(
% 1.55/0.60    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.55/0.60    inference(cnf_transformation,[],[f18])).
% 1.55/0.60  fof(f136,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~sP3(X0,k1_xboole_0,X1)) )),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f76,f30])).
% 1.55/0.60  fof(f30,plain,(
% 1.55/0.60    ( ! [X0,X3,X1] : (r2_hidden(sK4(X0,X1,X3),X1) | ~sP3(X3,X1,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f18])).
% 1.55/0.60  fof(f397,plain,(
% 1.55/0.60    ( ! [X1] : (k10_relat_1(sK1,k1_xboole_0) = k10_relat_1(sK1,X1) | ~r1_xboole_0(k2_relat_1(sK1),X1)) )),
% 1.55/0.60    inference(superposition,[],[f381,f67])).
% 1.55/0.60  fof(f67,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(definition_unfolding,[],[f43,f37])).
% 1.55/0.60  fof(f37,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f9])).
% 1.55/0.60  fof(f9,axiom,(
% 1.55/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.55/0.60  fof(f43,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f3])).
% 1.55/0.60  fof(f3,axiom,(
% 1.55/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.55/0.60  fof(f381,plain,(
% 1.55/0.60    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k1_setfam_1(k2_tarski(k2_relat_1(sK1),X0)))) )),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f26,f66])).
% 1.55/0.60  fof(f66,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k2_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.55/0.60    inference(definition_unfolding,[],[f41,f37])).
% 1.55/0.60  fof(f41,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f21,plain,(
% 1.55/0.60    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.55/0.60    inference(ennf_transformation,[],[f13])).
% 1.55/0.60  fof(f13,axiom,(
% 1.55/0.60    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.55/0.60  fof(f25,plain,(
% 1.55/0.60    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.55/0.60    inference(cnf_transformation,[],[f17])).
% 1.55/0.60  fof(f902,plain,(
% 1.55/0.60    r2_hidden(sK6(k2_relat_1(sK1),sK0),sK0)),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f853,f56])).
% 1.55/0.60  fof(f56,plain,(
% 1.55/0.60    ( ! [X0,X3,X1] : (~sP12(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  fof(f853,plain,(
% 1.55/0.60    sP12(sK6(k2_relat_1(sK1),sK0),k4_xboole_0(sK0,k2_relat_1(sK1)),sK0)),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f443,f201])).
% 1.55/0.60  fof(f201,plain,(
% 1.55/0.60    ( ! [X4,X5,X3] : (~r2_hidden(X5,k1_setfam_1(k2_tarski(X3,X4))) | sP12(X5,k4_xboole_0(X3,X4),X3)) )),
% 1.55/0.60    inference(superposition,[],[f73,f63])).
% 1.55/0.60  fof(f63,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f38,f37])).
% 1.55/0.60  fof(f38,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f6])).
% 1.55/0.60  fof(f6,axiom,(
% 1.55/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.55/0.60  fof(f73,plain,(
% 1.55/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | sP12(X3,X1,X0)) )),
% 1.55/0.60    inference(equality_resolution,[],[f59])).
% 1.55/0.60  fof(f59,plain,(
% 1.55/0.60    ( ! [X2,X0,X3,X1] : (sP12(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  fof(f443,plain,(
% 1.55/0.60    r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(sK0,k2_relat_1(sK1))))),
% 1.55/0.60    inference(forward_demodulation,[],[f439,f62])).
% 1.55/0.60  fof(f62,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f36,f37,f37])).
% 1.55/0.60  fof(f36,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f1])).
% 1.55/0.60  fof(f1,axiom,(
% 1.55/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.55/0.60  fof(f439,plain,(
% 1.55/0.60    r2_hidden(sK6(k2_relat_1(sK1),sK0),k1_setfam_1(k2_tarski(k2_relat_1(sK1),sK0)))),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f434,f64])).
% 1.55/0.60  fof(f64,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(definition_unfolding,[],[f40,f37])).
% 1.55/0.60  fof(f40,plain,(
% 1.55/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK6(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f20])).
% 1.55/0.60  fof(f20,plain,(
% 1.55/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.55/0.60    inference(ennf_transformation,[],[f16])).
% 1.55/0.60  fof(f16,plain,(
% 1.55/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.55/0.60    inference(rectify,[],[f4])).
% 1.55/0.60  fof(f4,axiom,(
% 1.55/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.55/0.60  fof(f901,plain,(
% 1.55/0.60    ~r2_hidden(sK6(k2_relat_1(sK1),sK0),k4_xboole_0(sK0,k2_relat_1(sK1)))),
% 1.55/0.60    inference(unit_resulting_resolution,[],[f853,f57])).
% 1.55/0.60  fof(f57,plain,(
% 1.55/0.60    ( ! [X0,X3,X1] : (~sP12(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  % SZS output end Proof for theBenchmark
% 1.55/0.60  % (12028)------------------------------
% 1.55/0.60  % (12028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (12028)Termination reason: Refutation
% 1.55/0.60  
% 1.55/0.60  % (12028)Memory used [KB]: 7291
% 1.55/0.60  % (12028)Time elapsed: 0.193 s
% 1.55/0.60  % (12028)------------------------------
% 1.55/0.60  % (12028)------------------------------
% 1.55/0.60  % (12003)Success in time 0.24 s
%------------------------------------------------------------------------------
