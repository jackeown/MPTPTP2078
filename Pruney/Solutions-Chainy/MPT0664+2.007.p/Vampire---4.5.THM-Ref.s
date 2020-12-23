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
% DateTime   : Thu Dec  3 12:53:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  74 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 235 expanded)
%              Number of equality atoms :   41 (  70 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f17,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,X1)
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f68,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f66,f34])).

fof(f34,plain,(
    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) ),
    inference(resolution,[],[f33,f16])).

fof(f16,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(subsumption_resolution,[],[f32,f19])).

fof(f19,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(subsumption_resolution,[],[f27,f18])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(X1,X2) = X2
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f66,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f58,f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1) ) ),
    inference(forward_demodulation,[],[f57,f35])).

fof(f35,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f20,f14])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) ) ),
    inference(subsumption_resolution,[],[f56,f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) ) ),
    inference(subsumption_resolution,[],[f53,f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f49,f31])).

fof(f31,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f30,f19])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f26,f18])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k5_relat_1(X0,sK2),X1) = k1_funct_1(sK2,k1_funct_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f47,f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(k5_relat_1(X0,sK2),X1) = k1_funct_1(sK2,k1_funct_1(X0,X1)) ) ),
    inference(resolution,[],[f25,f15])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:40:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (4962)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.44  % (4962)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f68,f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.44    inference(flattening,[],[f7])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.44    inference(negated_conjecture,[],[f5])).
% 0.20/0.44  fof(f5,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)),
% 0.20/0.44    inference(forward_demodulation,[],[f66,f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    sK0 = k1_funct_1(k6_relat_1(sK1),sK0)),
% 0.20/0.44    inference(resolution,[],[f33,f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    r2_hidden(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_funct_1(k6_relat_1(X0),X2) = X2) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f32,f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X2,X0] : (~v1_funct_1(k6_relat_1(X0)) | ~r2_hidden(X2,X0) | k1_funct_1(k6_relat_1(X0),X2) = X2) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f27,f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X2,X0] : (~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~r2_hidden(X2,X0) | k1_funct_1(k6_relat_1(X0),X2) = X2) )),
% 0.20/0.44    inference(equality_resolution,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,X0) | k1_funct_1(X1,X2) = X2 | k6_relat_1(X0) != X1) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))),
% 0.20/0.44    inference(resolution,[],[f58,f16])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1)) = k1_funct_1(k7_relat_1(sK2,X0),X1)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f57,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 0.20/0.44    inference(resolution,[],[f20,f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    v1_relat_1(sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f56,f19])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_funct_1(k6_relat_1(X0)) | k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f53,f18])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | k1_funct_1(k5_relat_1(k6_relat_1(X0),sK2),X1) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X0),X1))) )),
% 0.20/0.44    inference(superposition,[],[f49,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f30,f19])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f26,f18])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.44    inference(equality_resolution,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(k5_relat_1(X0,sK2),X1) = k1_funct_1(sK2,k1_funct_1(X0,X1))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f47,f14])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(k5_relat_1(X0,sK2),X1) = k1_funct_1(sK2,k1_funct_1(X0,X1))) )),
% 0.20/0.44    inference(resolution,[],[f25,f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    v1_funct_1(sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (4962)------------------------------
% 0.20/0.44  % (4962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (4962)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (4962)Memory used [KB]: 1663
% 0.20/0.44  % (4962)Time elapsed: 0.029 s
% 0.20/0.44  % (4962)------------------------------
% 0.20/0.44  % (4962)------------------------------
% 0.20/0.44  % (4944)Success in time 0.082 s
%------------------------------------------------------------------------------
