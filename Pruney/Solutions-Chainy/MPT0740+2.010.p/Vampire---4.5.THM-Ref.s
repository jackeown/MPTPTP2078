%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 191 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  256 ( 494 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1099,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f162,f645,f762,f784,f1098])).

fof(f1098,plain,
    ( spl3_10
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f1097])).

fof(f1097,plain,
    ( $false
    | spl3_10
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f1096,f157])).

fof(f157,plain,
    ( ~ v1_ordinal1(k3_tarski(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_10
  <=> v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1096,plain,
    ( v1_ordinal1(k3_tarski(sK0))
    | spl3_10
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f1093,f164])).

fof(f164,plain,
    ( ~ r1_tarski(sK2(k3_tarski(sK0)),k3_tarski(sK0))
    | spl3_10 ),
    inference(resolution,[],[f157,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) )
     => v1_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f1093,plain,
    ( r1_tarski(sK2(k3_tarski(sK0)),k3_tarski(sK0))
    | v1_ordinal1(k3_tarski(sK0))
    | ~ spl3_30 ),
    inference(resolution,[],[f947,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f947,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_tarski(sK0))
        | r1_tarski(X0,k3_tarski(sK0)) )
    | ~ spl3_30 ),
    inference(resolution,[],[f718,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

% (13999)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f718,plain,
    ( r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl3_30 ),
    inference(resolution,[],[f574,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f574,plain,
    ( r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl3_30
  <=> r1_tarski(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f784,plain,
    ( spl3_31
    | spl3_11
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f715,f573,f159,f577])).

fof(f577,plain,
    ( spl3_31
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f159,plain,
    ( spl3_11
  <=> r2_xboole_0(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f715,plain,
    ( r2_xboole_0(k3_tarski(sK0),sK0)
    | sK0 = k3_tarski(sK0)
    | ~ spl3_30 ),
    inference(resolution,[],[f574,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f762,plain,(
    ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f726,f39])).

fof(f39,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & v3_ordinal1(X0) )
   => ( ~ v3_ordinal1(k3_tarski(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f726,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f40,f579])).

fof(f579,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f577])).

fof(f40,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f645,plain,(
    spl3_30 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | spl3_30 ),
    inference(subsumption_resolution,[],[f587,f584])).

fof(f584,plain,
    ( ~ r1_tarski(sK1(sK0,sK0),sK0)
    | spl3_30 ),
    inference(resolution,[],[f575,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f575,plain,
    ( ~ r1_tarski(k3_tarski(sK0),sK0)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f573])).

fof(f587,plain,
    ( r1_tarski(sK1(sK0,sK0),sK0)
    | spl3_30 ),
    inference(resolution,[],[f583,f399])).

fof(f399,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_tarski(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f398,f60])).

fof(f60,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK0)
      | v3_ordinal1(X6) ) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f398,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f396,f39])).

fof(f396,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_tarski(X0,sK0)
      | ~ v3_ordinal1(sK0)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f395,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f395,plain,(
    ! [X3] :
      ( r1_ordinal1(X3,sK0)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f392,f352])).

fof(f352,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r1_ordinal1(sK0,X3) ) ),
    inference(subsumption_resolution,[],[f349,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f349,plain,(
    ! [X3] :
      ( r1_tarski(sK0,X3)
      | ~ r2_hidden(X3,sK0)
      | ~ r1_ordinal1(sK0,X3) ) ),
    inference(resolution,[],[f87,f39])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_tarski(sK0,X0)
      | ~ r2_hidden(X0,X1)
      | ~ r1_ordinal1(sK0,X0) ) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(sK0,X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f39,f45])).

fof(f392,plain,(
    ! [X3] :
      ( r1_ordinal1(X3,sK0)
      | ~ r2_hidden(X3,sK0)
      | r1_ordinal1(sK0,X3) ) ),
    inference(resolution,[],[f225,f39])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,sK0)
      | ~ r2_hidden(X0,X1)
      | r1_ordinal1(sK0,X0) ) ),
    inference(resolution,[],[f58,f48])).

fof(f58,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(X4)
      | r1_ordinal1(sK0,X4)
      | r1_ordinal1(X4,sK0) ) ),
    inference(resolution,[],[f39,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f583,plain,
    ( r2_hidden(sK1(sK0,sK0),sK0)
    | spl3_30 ),
    inference(resolution,[],[f575,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f162,plain,
    ( ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f153,f159,f155])).

fof(f153,plain,
    ( ~ r2_xboole_0(k3_tarski(sK0),sK0)
    | ~ v1_ordinal1(k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f152,f39])).

fof(f152,plain,
    ( ~ r2_xboole_0(k3_tarski(sK0),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v1_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f85,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f85,plain,(
    ~ r2_hidden(k3_tarski(sK0),sK0) ),
    inference(resolution,[],[f62,f39])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(k3_tarski(sK0),X0) ) ),
    inference(resolution,[],[f40,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (13996)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (13986)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (13994)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (13981)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (14000)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (13983)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (13995)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (13989)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (13981)Refutation not found, incomplete strategy% (13981)------------------------------
% 0.20/0.49  % (13981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13981)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13981)Memory used [KB]: 6012
% 0.20/0.49  % (13981)Time elapsed: 0.081 s
% 0.20/0.49  % (13981)------------------------------
% 0.20/0.49  % (13981)------------------------------
% 0.20/0.49  % (13995)Refutation not found, incomplete strategy% (13995)------------------------------
% 0.20/0.49  % (13995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13984)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (13985)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (13984)Refutation not found, incomplete strategy% (13984)------------------------------
% 0.20/0.49  % (13984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13984)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13984)Memory used [KB]: 10618
% 0.20/0.49  % (13984)Time elapsed: 0.089 s
% 0.20/0.49  % (13984)------------------------------
% 0.20/0.49  % (13984)------------------------------
% 0.20/0.49  % (13988)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (13982)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (13982)Refutation not found, incomplete strategy% (13982)------------------------------
% 0.20/0.50  % (13982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13982)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13982)Memory used [KB]: 10490
% 0.20/0.50  % (13982)Time elapsed: 0.083 s
% 0.20/0.50  % (13982)------------------------------
% 0.20/0.50  % (13982)------------------------------
% 0.20/0.50  % (13990)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (14001)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (14000)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (13992)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (13987)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (14001)Refutation not found, incomplete strategy% (14001)------------------------------
% 0.20/0.50  % (14001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14001)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (14001)Memory used [KB]: 10490
% 0.20/0.50  % (14001)Time elapsed: 0.096 s
% 0.20/0.50  % (14001)------------------------------
% 0.20/0.50  % (14001)------------------------------
% 0.20/0.50  % (13995)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13995)Memory used [KB]: 10618
% 0.20/0.50  % (13995)Time elapsed: 0.044 s
% 0.20/0.50  % (13995)------------------------------
% 0.20/0.50  % (13995)------------------------------
% 0.20/0.50  % (13998)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (13992)Refutation not found, incomplete strategy% (13992)------------------------------
% 0.20/0.50  % (13992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13992)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13992)Memory used [KB]: 10618
% 0.20/0.50  % (13992)Time elapsed: 0.100 s
% 0.20/0.50  % (13992)------------------------------
% 0.20/0.50  % (13992)------------------------------
% 0.20/0.50  % (13997)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (13993)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f1099,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f162,f645,f762,f784,f1098])).
% 0.20/0.51  fof(f1098,plain,(
% 0.20/0.51    spl3_10 | ~spl3_30),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1097])).
% 0.20/0.51  fof(f1097,plain,(
% 0.20/0.51    $false | (spl3_10 | ~spl3_30)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1096,f157])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ~v1_ordinal1(k3_tarski(sK0)) | spl3_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f155])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    spl3_10 <=> v1_ordinal1(k3_tarski(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.51  fof(f1096,plain,(
% 0.20/0.51    v1_ordinal1(k3_tarski(sK0)) | (spl3_10 | ~spl3_30)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1093,f164])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    ~r1_tarski(sK2(k3_tarski(sK0)),k3_tarski(sK0)) | spl3_10),
% 0.20/0.51    inference(resolution,[],[f157,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK2(X0),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) | (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)) => v1_ordinal1(X0))),
% 0.20/0.51    inference(unused_predicate_definition_removal,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.20/0.51  fof(f1093,plain,(
% 0.20/0.51    r1_tarski(sK2(k3_tarski(sK0)),k3_tarski(sK0)) | v1_ordinal1(k3_tarski(sK0)) | ~spl3_30),
% 0.20/0.51    inference(resolution,[],[f947,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f947,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k3_tarski(sK0)) | r1_tarski(X0,k3_tarski(sK0))) ) | ~spl3_30),
% 0.20/0.51    inference(resolution,[],[f718,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  % (13999)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.20/0.51  fof(f718,plain,(
% 0.20/0.51    r1_tarski(k3_tarski(k3_tarski(sK0)),k3_tarski(sK0)) | ~spl3_30),
% 0.20/0.51    inference(resolution,[],[f574,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.20/0.51  fof(f574,plain,(
% 0.20/0.51    r1_tarski(k3_tarski(sK0),sK0) | ~spl3_30),
% 0.20/0.51    inference(avatar_component_clause,[],[f573])).
% 0.20/0.51  fof(f573,plain,(
% 0.20/0.51    spl3_30 <=> r1_tarski(k3_tarski(sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.51  fof(f784,plain,(
% 0.20/0.51    spl3_31 | spl3_11 | ~spl3_30),
% 0.20/0.51    inference(avatar_split_clause,[],[f715,f573,f159,f577])).
% 0.20/0.51  fof(f577,plain,(
% 0.20/0.51    spl3_31 <=> sK0 = k3_tarski(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    spl3_11 <=> r2_xboole_0(k3_tarski(sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.51  fof(f715,plain,(
% 0.20/0.51    r2_xboole_0(k3_tarski(sK0),sK0) | sK0 = k3_tarski(sK0) | ~spl3_30),
% 0.20/0.51    inference(resolution,[],[f574,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.20/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.51  fof(f762,plain,(
% 0.20/0.51    ~spl3_31),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f761])).
% 0.20/0.51  fof(f761,plain,(
% 0.20/0.51    $false | ~spl3_31),
% 0.20/0.51    inference(subsumption_resolution,[],[f726,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    v3_ordinal1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ~v3_ordinal1(k3_tarski(sK0)) & v3_ordinal1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0)) => (~v3_ordinal1(k3_tarski(sK0)) & v3_ordinal1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f11])).
% 0.20/0.51  fof(f11,conjecture,(
% 0.20/0.51    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).
% 0.20/0.51  fof(f726,plain,(
% 0.20/0.51    ~v3_ordinal1(sK0) | ~spl3_31),
% 0.20/0.51    inference(backward_demodulation,[],[f40,f579])).
% 0.20/0.51  fof(f579,plain,(
% 0.20/0.51    sK0 = k3_tarski(sK0) | ~spl3_31),
% 0.20/0.51    inference(avatar_component_clause,[],[f577])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ~v3_ordinal1(k3_tarski(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f645,plain,(
% 0.20/0.51    spl3_30),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f644])).
% 0.20/0.51  fof(f644,plain,(
% 0.20/0.51    $false | spl3_30),
% 0.20/0.51    inference(subsumption_resolution,[],[f587,f584])).
% 0.20/0.51  fof(f584,plain,(
% 0.20/0.51    ~r1_tarski(sK1(sK0,sK0),sK0) | spl3_30),
% 0.20/0.51    inference(resolution,[],[f575,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK1(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.20/0.51  fof(f575,plain,(
% 0.20/0.51    ~r1_tarski(k3_tarski(sK0),sK0) | spl3_30),
% 0.20/0.51    inference(avatar_component_clause,[],[f573])).
% 0.20/0.51  fof(f587,plain,(
% 0.20/0.51    r1_tarski(sK1(sK0,sK0),sK0) | spl3_30),
% 0.20/0.51    inference(resolution,[],[f583,f399])).
% 0.20/0.51  fof(f399,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(X0,sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f398,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X6] : (~r2_hidden(X6,sK0) | v3_ordinal1(X6)) )),
% 0.20/0.51    inference(resolution,[],[f39,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.20/0.51  fof(f398,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(X0,sK0) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f396,f39])).
% 0.20/0.51  fof(f396,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(X0,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(resolution,[],[f395,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.51  fof(f395,plain,(
% 0.20/0.51    ( ! [X3] : (r1_ordinal1(X3,sK0) | ~r2_hidden(X3,sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f392,f352])).
% 0.20/0.51  fof(f352,plain,(
% 0.20/0.51    ( ! [X3] : (~r2_hidden(X3,sK0) | ~r1_ordinal1(sK0,X3)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f349,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.51  fof(f349,plain,(
% 0.20/0.51    ( ! [X3] : (r1_tarski(sK0,X3) | ~r2_hidden(X3,sK0) | ~r1_ordinal1(sK0,X3)) )),
% 0.20/0.51    inference(resolution,[],[f87,f39])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_tarski(sK0,X0) | ~r2_hidden(X0,X1) | ~r1_ordinal1(sK0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f54,f48])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0] : (~v3_ordinal1(X0) | ~r1_ordinal1(sK0,X0) | r1_tarski(sK0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f39,f45])).
% 0.20/0.51  fof(f392,plain,(
% 0.20/0.51    ( ! [X3] : (r1_ordinal1(X3,sK0) | ~r2_hidden(X3,sK0) | r1_ordinal1(sK0,X3)) )),
% 0.20/0.51    inference(resolution,[],[f225,f39])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,sK0) | ~r2_hidden(X0,X1) | r1_ordinal1(sK0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f58,f48])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X4] : (~v3_ordinal1(X4) | r1_ordinal1(sK0,X4) | r1_ordinal1(X4,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f39,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.20/0.51  fof(f583,plain,(
% 0.20/0.51    r2_hidden(sK1(sK0,sK0),sK0) | spl3_30),
% 0.20/0.51    inference(resolution,[],[f575,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ~spl3_10 | ~spl3_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f153,f159,f155])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ~r2_xboole_0(k3_tarski(sK0),sK0) | ~v1_ordinal1(k3_tarski(sK0))),
% 0.20/0.51    inference(subsumption_resolution,[],[f152,f39])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ~r2_xboole_0(k3_tarski(sK0),sK0) | ~v3_ordinal1(sK0) | ~v1_ordinal1(k3_tarski(sK0))),
% 0.20/0.51    inference(resolution,[],[f85,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~r2_hidden(k3_tarski(sK0),sK0)),
% 0.20/0.51    inference(resolution,[],[f62,f39])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (~v3_ordinal1(X0) | ~r2_hidden(k3_tarski(sK0),X0)) )),
% 0.20/0.51    inference(resolution,[],[f40,f48])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (14000)------------------------------
% 0.20/0.51  % (14000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14000)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (14000)Memory used [KB]: 6524
% 0.20/0.51  % (14000)Time elapsed: 0.096 s
% 0.20/0.51  % (14000)------------------------------
% 0.20/0.51  % (14000)------------------------------
% 0.20/0.51  % (13980)Success in time 0.156 s
%------------------------------------------------------------------------------
