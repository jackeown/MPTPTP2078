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
% DateTime   : Thu Dec  3 12:52:42 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    4
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    3 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,plain,(
    $false ),
    inference(resolution,[],[f7,f5])).

fof(f5,plain,(
    ~ v2_funct_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0] : ~ v2_funct_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f7,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:33:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.48  % (27381)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.23/0.48  % (27381)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f8,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(resolution,[],[f7,f5])).
% 0.23/0.48  fof(f5,plain,(
% 0.23/0.48    ~v2_funct_1(k6_relat_1(sK0))),
% 0.23/0.48    inference(cnf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,plain,(
% 0.23/0.48    ? [X0] : ~v2_funct_1(k6_relat_1(X0))),
% 0.23/0.48    inference(ennf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,negated_conjecture,(
% 0.23/0.48    ~! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.23/0.48    inference(negated_conjecture,[],[f2])).
% 0.23/0.48  fof(f2,conjecture,(
% 0.23/0.48    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.23/0.48  fof(f7,plain,(
% 0.23/0.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.23/0.48  % SZS output end Proof for theBenchmark
% 0.23/0.48  % (27381)------------------------------
% 0.23/0.48  % (27381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (27381)Termination reason: Refutation
% 0.23/0.48  
% 0.23/0.48  % (27381)Memory used [KB]: 5245
% 0.23/0.48  % (27381)Time elapsed: 0.051 s
% 0.23/0.48  % (27381)------------------------------
% 0.23/0.48  % (27381)------------------------------
% 0.23/0.48  % (27374)Success in time 0.111 s
%------------------------------------------------------------------------------
