%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  83 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 198 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f46,f51,f56,f60,f68])).

fof(f68,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f63,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f63,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(resolution,[],[f55,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_5
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k3_xboole_0(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f60,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f59,f37,f44])).

fof(f44,plain,
    ( spl2_3
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f37,plain,
    ( spl2_2
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f59,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f58,f25])).

fof(f58,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f57,f15])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_2 ),
    inference(resolution,[],[f38,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f38,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f56,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f52,f49,f54])).

fof(f49,plain,
    ( spl2_4
  <=> ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k3_xboole_0(sK0,sK1),X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f50,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f51,plain,
    ( spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f47,f44,f49])).

fof(f47,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl2_3 ),
    inference(resolution,[],[f45,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f45,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f46,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f42,f34,f44])).

fof(f34,plain,
    ( spl2_1
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f42,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f41,f20])).

fof(f41,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f40,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(resolution,[],[f18,f35])).

fof(f35,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f39,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f30,f37,f34])).

fof(f30,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f24,f16])).

fof(f16,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (30554)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (30554)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f39,f46,f51,f56,f60,f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ~spl2_5),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    $false | ~spl2_5),
% 0.21/0.43    inference(subsumption_resolution,[],[f63,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    v1_relat_1(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ~v1_relat_1(sK1) | ~spl2_5),
% 0.21/0.43    inference(resolution,[],[f55,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.21/0.43    inference(superposition,[],[f20,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK1),X0) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    spl2_5 <=> ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k3_xboole_0(sK0,sK1),X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ~spl2_3 | spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f59,f37,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl2_3 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl2_2 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_2),
% 0.21/0.44    inference(subsumption_resolution,[],[f58,f25])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_2),
% 0.21/0.44    inference(subsumption_resolution,[],[f57,f15])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ~v1_relat_1(sK1) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_2),
% 0.21/0.44    inference(resolution,[],[f38,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f37])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl2_5 | ~spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f52,f49,f54])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl2_4 <=> ! [X0] : (~m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k3_xboole_0(sK0,sK1),X0)) ) | ~spl2_4),
% 0.21/0.44    inference(resolution,[],[f50,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl2_4 | spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f47,f44,f49])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK0,sK1),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl2_3),
% 0.21/0.44    inference(resolution,[],[f45,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f44])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ~spl2_3 | spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f42,f34,f44])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl2_1 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.44    inference(subsumption_resolution,[],[f41,f20])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.44    inference(subsumption_resolution,[],[f40,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    v1_relat_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ~v1_relat_1(sK0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.44    inference(resolution,[],[f18,f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f34])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ~spl2_1 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f30,f37,f34])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))),
% 0.21/0.44    inference(resolution,[],[f24,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (30554)------------------------------
% 0.21/0.44  % (30554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30554)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (30554)Memory used [KB]: 10618
% 0.21/0.44  % (30554)Time elapsed: 0.006 s
% 0.21/0.44  % (30554)------------------------------
% 0.21/0.44  % (30554)------------------------------
% 0.21/0.44  % (30558)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (30550)Success in time 0.074 s
%------------------------------------------------------------------------------
