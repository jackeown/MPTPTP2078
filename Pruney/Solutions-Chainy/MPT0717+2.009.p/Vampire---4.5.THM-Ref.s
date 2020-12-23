%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   22 (  58 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 274 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f14,f16,f17,f21,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f21,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f14,f15,f18,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f18,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
    & r2_hidden(sK2,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
            & r2_hidden(X2,k1_relat_1(X1)) )
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
          & r2_hidden(X2,k1_relat_1(sK1)) )
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
        & r2_hidden(X2,k1_relat_1(sK1)) )
   => ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
      & r2_hidden(sK2,k1_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f15,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:05:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.43  % (2261)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.19/0.43  % (2261)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(unit_resulting_resolution,[],[f14,f16,f17,f21,f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f8])).
% 0.19/0.43  fof(f8,plain,(
% 0.19/0.43    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.43    inference(flattening,[],[f7])).
% 0.19/0.43  fof(f7,plain,(
% 0.19/0.43    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.43    inference(ennf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ~r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))),
% 0.19/0.43    inference(unit_resulting_resolution,[],[f14,f15,f18,f20])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.43    inference(flattening,[],[f9])).
% 0.19/0.43  fof(f9,plain,(
% 0.19/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.43    inference(ennf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ~r2_hidden(k1_funct_1(sK1,sK2),sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    (~r2_hidden(k1_funct_1(sK1,sK2),sK0) & r2_hidden(sK2,k1_relat_1(sK1))) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1)),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (? [X2] : (~r2_hidden(k1_funct_1(sK1,X2),sK0) & r2_hidden(X2,k1_relat_1(sK1))) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ? [X2] : (~r2_hidden(k1_funct_1(sK1,X2),sK0) & r2_hidden(X2,k1_relat_1(sK1))) => (~r2_hidden(k1_funct_1(sK1,sK2),sK0) & r2_hidden(sK2,k1_relat_1(sK1)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f6,plain,(
% 0.19/0.44    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.19/0.44    inference(flattening,[],[f5])).
% 0.19/0.44  fof(f5,plain,(
% 0.19/0.44    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & (v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.19/0.44    inference(negated_conjecture,[],[f3])).
% 0.19/0.44  fof(f3,conjecture,(
% 0.19/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    v5_relat_1(sK1,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f13])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    r2_hidden(sK2,k1_relat_1(sK1))),
% 0.19/0.44    inference(cnf_transformation,[],[f13])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    v1_funct_1(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f13])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    v1_relat_1(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f13])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (2261)------------------------------
% 0.19/0.44  % (2261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (2261)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (2261)Memory used [KB]: 9850
% 0.19/0.44  % (2261)Time elapsed: 0.056 s
% 0.19/0.44  % (2261)------------------------------
% 0.19/0.44  % (2261)------------------------------
% 0.19/0.44  % (2257)Success in time 0.089 s
%------------------------------------------------------------------------------
