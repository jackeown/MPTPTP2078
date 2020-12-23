%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 100 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 267 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f75,f103,f107,f111,f115,f123])).

fof(f123,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_6
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4
    | spl3_6
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f36,f36,f51,f31,f101,f61,f74,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

fof(f74,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_6
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,(
    ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0) ),
    inference(superposition,[],[f53,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f28,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f101,plain,
    ( v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_9
  <=> v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f31,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f36,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f115,plain,
    ( ~ spl3_2
    | spl3_9 ),
    inference(avatar_split_clause,[],[f113,f100,f39])).

fof(f39,plain,
    ( spl3_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f113,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_9 ),
    inference(resolution,[],[f102,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f102,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f111,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f31,f98])).

fof(f98,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_8
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f107,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f22,f94])).

fof(f94,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_7
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f103,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f90,f68,f34,f100,f39,f96,f92])).

fof(f68,plain,
    ( spl3_5
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl3_5 ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(resolution,[],[f21,f70])).

fof(f70,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f75,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_3 ),
    inference(avatar_split_clause,[],[f64,f44,f72,f68])).

fof(f44,plain,
    ( spl3_3
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))
    | spl3_3 ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f49])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:57:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (28650)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.49  % (28659)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (28651)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (28659)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f75,f103,f107,f111,f115,f123])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~spl3_1 | ~spl3_4 | spl3_6 | ~spl3_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    $false | (~spl3_1 | ~spl3_4 | spl3_6 | ~spl3_9)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f36,f36,f51,f31,f101,f61,f74,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl3_6 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) )),
% 0.22/0.50    inference(superposition,[],[f53,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f28,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    v1_relat_1(k3_xboole_0(sK1,sK2)) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl3_9 <=> v1_relat_1(k3_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl3_4 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    v1_relat_1(sK0) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    spl3_1 <=> v1_relat_1(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ~spl3_2 | spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f113,f100,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    spl3_2 <=> v1_relat_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ~v1_relat_1(sK1) | spl3_9),
% 0.22/0.50    inference(resolution,[],[f102,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f100])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    $false | spl3_8),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f31,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK0) | spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl3_8 <=> r1_tarski(sK0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    spl3_7),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    $false | spl3_7),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f22,f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | spl3_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl3_7 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ~spl3_7 | ~spl3_8 | ~spl3_2 | ~spl3_9 | ~spl3_1 | spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f90,f68,f34,f100,f39,f96,f92])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl3_5 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | spl3_5),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~v1_relat_1(sK0) | spl3_5),
% 0.22/0.51    inference(resolution,[],[f21,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) | spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f68])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~spl3_5 | ~spl3_6 | spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f64,f44,f72,f68])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl3_3 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f30,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f49])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    v1_relat_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f44])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f39])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f34])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    v1_relat_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28659)------------------------------
% 0.22/0.51  % (28659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28659)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28659)Memory used [KB]: 6268
% 0.22/0.51  % (28659)Time elapsed: 0.015 s
% 0.22/0.51  % (28659)------------------------------
% 0.22/0.51  % (28659)------------------------------
% 0.22/0.51  % (28647)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (28643)Success in time 0.144 s
%------------------------------------------------------------------------------
