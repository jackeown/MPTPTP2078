%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:02 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 276 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  194 ( 656 expanded)
%              Number of equality atoms :   33 (  83 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f688,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f155,f181,f203,f679,f685,f687])).

fof(f687,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f686,f677,f153,f150])).

fof(f150,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f153,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f677,plain,
    ( spl3_6
  <=> v1_funct_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f686,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_6 ),
    inference(resolution,[],[f678,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f678,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f677])).

fof(f685,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f684,f674,f153,f150])).

fof(f674,plain,
    ( spl3_5
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f684,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f675,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f675,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f674])).

fof(f679,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f666,f50,f677,f674])).

fof(f50,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f666,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(resolution,[],[f633,f51])).

fof(f51,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f633,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))),X1)
      | ~ v1_funct_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(backward_demodulation,[],[f256,f294])).

fof(f294,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k10_relat_1(sK2,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,k10_relat_1(sK2,X1))) ),
    inference(superposition,[],[f72,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK2,X2))) = k3_xboole_0(k3_xboole_0(X0,X1),k10_relat_1(sK2,X2)) ),
    inference(global_subsumption,[],[f25,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK2,X2))) = k3_xboole_0(k3_xboole_0(X0,X1),k10_relat_1(sK2,X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f91,f56])).

fof(f56,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f35,f25])).

% (3563)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (3561)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK2,X2))) = k10_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1)),X2)
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f90,f58])).

fof(f58,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f36,f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK2,X2)))
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f88,f56])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK2,X0),X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f57,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f57,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4),X5) = k3_xboole_0(X4,k10_relat_1(k7_relat_1(X2,X3),X5))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f35,f33])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X2),k10_relat_1(sK2,X3)) = k3_xboole_0(X2,k10_relat_1(sK2,X3)) ),
    inference(forward_demodulation,[],[f66,f56])).

fof(f66,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X2),k10_relat_1(sK2,X3)) = k10_relat_1(k7_relat_1(sK2,X2),X3) ),
    inference(superposition,[],[f56,f61])).

fof(f61,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f58,f41])).

fof(f41,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0) ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(f256,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,k3_xboole_0(X0,k10_relat_1(sK2,X1)))),X1)
      | ~ v1_funct_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(forward_demodulation,[],[f60,f78])).

fof(f78,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(global_subsumption,[],[f25,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f76,f39])).

fof(f39,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f30,f25])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f74,f58])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(k7_relat_1(X1,X2),X3) = k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f30,f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),k3_xboole_0(X0,k10_relat_1(sK2,X1))),X1)
      | ~ v1_funct_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f32,f56])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f203,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f154,f26])).

fof(f154,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f181,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f151,f25])).

fof(f151,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f150])).

fof(f155,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f148,f53,f153,f150])).

fof(f53,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f148,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(resolution,[],[f142,f33])).

fof(f142,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_2 ),
    inference(resolution,[],[f113,f54])).

fof(f54,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(forward_demodulation,[],[f43,f78])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f29,f39])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f55,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f53,f50])).

fof(f46,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(resolution,[],[f37,f38])).

fof(f38,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f27,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:48:11 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.51  % (3554)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.23/0.51  % (3543)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.23/0.51  % (3555)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.23/0.51  % (3556)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.23/0.52  % (3542)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.23/0.52  % (3560)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.23/0.52  % (3564)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.23/0.52  % (3565)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.23/0.52  % (3557)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.23/0.52  % (3541)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.23/0.52  % (3547)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.23/0.52  % (3545)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.23/0.52  % (3565)Refutation not found, incomplete strategy% (3565)------------------------------
% 0.23/0.52  % (3565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (3545)Refutation not found, incomplete strategy% (3545)------------------------------
% 0.23/0.52  % (3545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (3545)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (3545)Memory used [KB]: 10490
% 0.23/0.53  % (3545)Time elapsed: 0.102 s
% 0.23/0.53  % (3545)------------------------------
% 0.23/0.53  % (3545)------------------------------
% 0.23/0.53  % (3550)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.23/0.53  % (3549)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.53  % (3553)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.23/0.53  % (3565)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (3565)Memory used [KB]: 10618
% 0.23/0.53  % (3565)Time elapsed: 0.049 s
% 0.23/0.53  % (3565)------------------------------
% 0.23/0.53  % (3565)------------------------------
% 0.23/0.53  % (3551)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.23/0.53  % (3546)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.53  % (3552)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.23/0.53  % (3548)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.23/0.53  % (3558)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.54  % (3559)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.23/0.54  % (3562)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.23/0.55  % (3554)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f688,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(avatar_sat_refutation,[],[f55,f155,f181,f203,f679,f685,f687])).
% 0.23/0.55  fof(f687,plain,(
% 0.23/0.55    ~spl3_3 | ~spl3_4 | spl3_6),
% 0.23/0.55    inference(avatar_split_clause,[],[f686,f677,f153,f150])).
% 0.23/0.55  fof(f150,plain,(
% 0.23/0.55    spl3_3 <=> v1_relat_1(sK2)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.55  fof(f153,plain,(
% 0.23/0.55    spl3_4 <=> v1_funct_1(sK2)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.55  fof(f677,plain,(
% 0.23/0.55    spl3_6 <=> v1_funct_1(k7_relat_1(sK2,sK0))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.55  fof(f686,plain,(
% 0.23/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_6),
% 0.23/0.55    inference(resolution,[],[f678,f34])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f20])).
% 0.23/0.55  fof(f20,plain,(
% 0.23/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(flattening,[],[f19])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.23/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.23/0.55  fof(f678,plain,(
% 0.23/0.55    ~v1_funct_1(k7_relat_1(sK2,sK0)) | spl3_6),
% 0.23/0.55    inference(avatar_component_clause,[],[f677])).
% 0.23/0.55  fof(f685,plain,(
% 0.23/0.55    ~spl3_3 | ~spl3_4 | spl3_5),
% 0.23/0.55    inference(avatar_split_clause,[],[f684,f674,f153,f150])).
% 0.23/0.55  fof(f674,plain,(
% 0.23/0.55    spl3_5 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.55  fof(f684,plain,(
% 0.23/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_5),
% 0.23/0.55    inference(resolution,[],[f675,f33])).
% 0.23/0.55  fof(f33,plain,(
% 0.23/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f20])).
% 0.23/0.55  fof(f675,plain,(
% 0.23/0.55    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_5),
% 0.23/0.55    inference(avatar_component_clause,[],[f674])).
% 0.23/0.55  fof(f679,plain,(
% 0.23/0.55    ~spl3_5 | ~spl3_6 | spl3_1),
% 0.23/0.55    inference(avatar_split_clause,[],[f666,f50,f677,f674])).
% 0.23/0.55  fof(f50,plain,(
% 0.23/0.55    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.55  fof(f666,plain,(
% 0.23/0.55    ~v1_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_1),
% 0.23/0.55    inference(resolution,[],[f633,f51])).
% 0.23/0.55  fof(f51,plain,(
% 0.23/0.55    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) | spl3_1),
% 0.23/0.55    inference(avatar_component_clause,[],[f50])).
% 0.23/0.55  fof(f633,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))),X1) | ~v1_funct_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.55    inference(backward_demodulation,[],[f256,f294])).
% 0.23/0.55  fof(f294,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k10_relat_1(sK2,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,k10_relat_1(sK2,X1)))) )),
% 0.23/0.55    inference(superposition,[],[f72,f93])).
% 0.23/0.55  fof(f93,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK2,X2))) = k3_xboole_0(k3_xboole_0(X0,X1),k10_relat_1(sK2,X2))) )),
% 0.23/0.55    inference(global_subsumption,[],[f25,f92])).
% 0.23/0.55  fof(f92,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK2,X2))) = k3_xboole_0(k3_xboole_0(X0,X1),k10_relat_1(sK2,X2)) | ~v1_relat_1(sK2)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f91,f56])).
% 0.23/0.55  fof(f56,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK2,X1))) )),
% 0.23/0.55    inference(resolution,[],[f35,f25])).
% 0.23/0.55  % (3563)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.23/0.55  % (3561)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.23/0.56  fof(f35,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f21])).
% 0.23/0.56  fof(f21,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.23/0.56    inference(ennf_transformation,[],[f8])).
% 0.23/0.56  fof(f8,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.23/0.56  fof(f91,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK2,X2))) = k10_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1)),X2) | ~v1_relat_1(sK2)) )),
% 0.23/0.56    inference(forward_demodulation,[],[f90,f58])).
% 0.23/0.56  fof(f58,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.23/0.56    inference(resolution,[],[f36,f25])).
% 0.23/0.56  fof(f36,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f22])).
% 0.23/0.56  fof(f22,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.23/0.56    inference(ennf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.23/0.56  fof(f90,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k3_xboole_0(X1,k3_xboole_0(X0,k10_relat_1(sK2,X2))) | ~v1_relat_1(sK2)) )),
% 0.23/0.56    inference(forward_demodulation,[],[f88,f56])).
% 0.23/0.56  fof(f88,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1),X2) = k3_xboole_0(X1,k10_relat_1(k7_relat_1(sK2,X0),X2)) | ~v1_relat_1(sK2)) )),
% 0.23/0.56    inference(resolution,[],[f57,f26])).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    v1_funct_1(sK2)),
% 0.23/0.56    inference(cnf_transformation,[],[f13])).
% 0.23/0.56  fof(f13,plain,(
% 0.23/0.56    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.23/0.56    inference(flattening,[],[f12])).
% 0.23/0.56  fof(f12,plain,(
% 0.23/0.56    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.23/0.56    inference(ennf_transformation,[],[f11])).
% 0.23/0.56  fof(f11,negated_conjecture,(
% 0.23/0.56    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.23/0.56    inference(negated_conjecture,[],[f10])).
% 0.23/0.56  fof(f10,conjecture,(
% 0.23/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 0.23/0.56  fof(f57,plain,(
% 0.23/0.56    ( ! [X4,X2,X5,X3] : (~v1_funct_1(X2) | k10_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4),X5) = k3_xboole_0(X4,k10_relat_1(k7_relat_1(X2,X3),X5)) | ~v1_relat_1(X2)) )),
% 0.23/0.56    inference(resolution,[],[f35,f33])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    v1_relat_1(sK2)),
% 0.23/0.56    inference(cnf_transformation,[],[f13])).
% 0.23/0.56  fof(f72,plain,(
% 0.23/0.56    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X2),k10_relat_1(sK2,X3)) = k3_xboole_0(X2,k10_relat_1(sK2,X3))) )),
% 0.23/0.56    inference(forward_demodulation,[],[f66,f56])).
% 0.23/0.56  fof(f66,plain,(
% 0.23/0.56    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X2),k10_relat_1(sK2,X3)) = k10_relat_1(k7_relat_1(sK2,X2),X3)) )),
% 0.23/0.56    inference(superposition,[],[f56,f61])).
% 0.23/0.56  fof(f61,plain,(
% 0.23/0.56    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k3_xboole_0(X0,X0))) )),
% 0.23/0.56    inference(superposition,[],[f58,f41])).
% 0.23/0.56  fof(f41,plain,(
% 0.23/0.56    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)) )),
% 0.23/0.56    inference(resolution,[],[f31,f25])).
% 0.23/0.56  fof(f31,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f16])).
% 0.23/0.56  fof(f16,plain,(
% 0.23/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).
% 0.23/0.56  fof(f256,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,k3_xboole_0(X0,k10_relat_1(sK2,X1)))),X1) | ~v1_funct_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.56    inference(forward_demodulation,[],[f60,f78])).
% 0.23/0.56  fof(f78,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.23/0.56    inference(global_subsumption,[],[f25,f77])).
% 0.23/0.56  fof(f77,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) | ~v1_relat_1(sK2)) )),
% 0.23/0.56    inference(forward_demodulation,[],[f76,f39])).
% 0.23/0.56  fof(f39,plain,(
% 0.23/0.56    ( ! [X0] : (k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.56    inference(resolution,[],[f30,f25])).
% 0.23/0.56  fof(f30,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f15])).
% 0.23/0.56  fof(f15,plain,(
% 0.23/0.56    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.23/0.56  fof(f76,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))) | ~v1_relat_1(sK2)) )),
% 0.23/0.56    inference(forward_demodulation,[],[f74,f58])).
% 0.23/0.56  fof(f74,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) | ~v1_relat_1(sK2)) )),
% 0.23/0.56    inference(resolution,[],[f40,f26])).
% 0.23/0.56  fof(f40,plain,(
% 0.23/0.56    ( ! [X2,X3,X1] : (~v1_funct_1(X1) | k9_relat_1(k7_relat_1(X1,X2),X3) = k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) | ~v1_relat_1(X1)) )),
% 0.23/0.56    inference(resolution,[],[f30,f33])).
% 0.23/0.56  fof(f60,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),k3_xboole_0(X0,k10_relat_1(sK2,X1))),X1) | ~v1_funct_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.56    inference(superposition,[],[f32,f56])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f18])).
% 0.23/0.56  fof(f18,plain,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.23/0.56    inference(flattening,[],[f17])).
% 0.23/0.56  fof(f17,plain,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.23/0.56    inference(ennf_transformation,[],[f9])).
% 0.23/0.56  fof(f9,axiom,(
% 0.23/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.23/0.56  fof(f203,plain,(
% 0.23/0.56    spl3_4),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f202])).
% 0.23/0.56  fof(f202,plain,(
% 0.23/0.56    $false | spl3_4),
% 0.23/0.56    inference(resolution,[],[f154,f26])).
% 0.23/0.56  fof(f154,plain,(
% 0.23/0.56    ~v1_funct_1(sK2) | spl3_4),
% 0.23/0.56    inference(avatar_component_clause,[],[f153])).
% 0.23/0.56  fof(f181,plain,(
% 0.23/0.56    spl3_3),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f180])).
% 0.23/0.56  fof(f180,plain,(
% 0.23/0.56    $false | spl3_3),
% 0.23/0.56    inference(resolution,[],[f151,f25])).
% 0.23/0.56  fof(f151,plain,(
% 0.23/0.56    ~v1_relat_1(sK2) | spl3_3),
% 0.23/0.56    inference(avatar_component_clause,[],[f150])).
% 0.23/0.56  fof(f155,plain,(
% 0.23/0.56    ~spl3_3 | ~spl3_4 | spl3_2),
% 0.23/0.56    inference(avatar_split_clause,[],[f148,f53,f153,f150])).
% 0.23/0.56  fof(f53,plain,(
% 0.23/0.56    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.56  fof(f148,plain,(
% 0.23/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_2),
% 0.23/0.56    inference(resolution,[],[f142,f33])).
% 0.23/0.56  fof(f142,plain,(
% 0.23/0.56    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_2),
% 0.23/0.56    inference(resolution,[],[f113,f54])).
% 0.23/0.56  fof(f54,plain,(
% 0.23/0.56    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | spl3_2),
% 0.23/0.56    inference(avatar_component_clause,[],[f53])).
% 0.23/0.56  fof(f113,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.56    inference(forward_demodulation,[],[f43,f78])).
% 0.23/0.56  fof(f43,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.56    inference(superposition,[],[f29,f39])).
% 0.23/0.56  fof(f29,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f14])).
% 0.23/0.56  fof(f14,plain,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.23/0.56    inference(ennf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.23/0.56  fof(f55,plain,(
% 0.23/0.56    ~spl3_1 | ~spl3_2),
% 0.23/0.56    inference(avatar_split_clause,[],[f46,f53,f50])).
% 0.23/0.56  fof(f46,plain,(
% 0.23/0.56    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 0.23/0.56    inference(resolution,[],[f37,f38])).
% 0.23/0.56  fof(f38,plain,(
% 0.23/0.56    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),
% 0.23/0.56    inference(backward_demodulation,[],[f27,f28])).
% 0.23/0.56  fof(f28,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.56  fof(f27,plain,(
% 0.23/0.56    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.23/0.56    inference(cnf_transformation,[],[f13])).
% 0.23/0.56  fof(f37,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f24])).
% 0.23/0.56  fof(f24,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.56    inference(flattening,[],[f23])).
% 0.23/0.56  fof(f23,plain,(
% 0.23/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.56    inference(ennf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (3554)------------------------------
% 0.23/0.56  % (3554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (3554)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (3554)Memory used [KB]: 11257
% 0.23/0.56  % (3554)Time elapsed: 0.138 s
% 0.23/0.56  % (3554)------------------------------
% 0.23/0.56  % (3554)------------------------------
% 0.23/0.56  % (3540)Success in time 0.189 s
%------------------------------------------------------------------------------
