%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  45 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 166 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f14])).

fof(f14,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

fof(f127,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f58,f31])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f58,plain,(
    r2_hidden(k4_tarski(sK5(sK2,sK1,sK8(k5_relat_1(sK2,sK1),sK0),sK0),sK0),sK1) ),
    inference(subsumption_resolution,[],[f57,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK1,sK8(k5_relat_1(sK2,sK1),sK0),sK0),sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f53,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK5(sK2,sK1,sK8(k5_relat_1(sK2,sK1),sK0),sK0),sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f28,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f28,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f37,plain,(
    r2_hidden(k4_tarski(sK8(k5_relat_1(sK2,sK1),sK0),sK0),k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f30,f13])).

fof(f13,plain,(
    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK8(X0,X2),X2),X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (21392)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.44  % (21392)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f129,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f127,f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).
% 0.22/0.44  fof(f127,plain,(
% 0.22/0.44    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.22/0.44    inference(resolution,[],[f58,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.22/0.44    inference(equality_resolution,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    r2_hidden(k4_tarski(sK5(sK2,sK1,sK8(k5_relat_1(sK2,sK1),sK0),sK0),sK0),sK1)),
% 0.22/0.45    inference(subsumption_resolution,[],[f57,f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    r2_hidden(k4_tarski(sK5(sK2,sK1,sK8(k5_relat_1(sK2,sK1),sK0),sK0),sK0),sK1) | ~v1_relat_1(sK2)),
% 0.22/0.45    inference(subsumption_resolution,[],[f53,f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    v1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK5(sK2,sK1,sK8(k5_relat_1(sK2,sK1),sK0),sK0),sK0),sK1) | ~v1_relat_1(sK2)),
% 0.22/0.45    inference(resolution,[],[f37,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(subsumption_resolution,[],[f28,f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 0.22/0.45    inference(equality_resolution,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    r2_hidden(k4_tarski(sK8(k5_relat_1(sK2,sK1),sK0),sK0),k5_relat_1(sK2,sK1))),
% 0.22/0.45    inference(resolution,[],[f30,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK8(X0,X2),X2),X0)) )),
% 0.22/0.45    inference(equality_resolution,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (21392)------------------------------
% 0.22/0.45  % (21392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (21392)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (21392)Memory used [KB]: 1918
% 0.22/0.45  % (21392)Time elapsed: 0.035 s
% 0.22/0.45  % (21392)------------------------------
% 0.22/0.45  % (21392)------------------------------
% 0.22/0.45  % (21374)Success in time 0.084 s
%------------------------------------------------------------------------------
