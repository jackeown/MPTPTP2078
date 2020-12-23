%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  46 expanded)
%              Number of leaves         :    2 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 291 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20,f17])).

fof(f17,plain,(
    ~ v5_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f16,f12])).

fof(f12,plain,(
    v5_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ v5_ordinal1(X2)
            | ~ v1_funct_1(X2)
            | ~ v5_relat_1(X2,X1)
            | ~ v1_relat_1(X2) )
          & v5_ordinal1(X2)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( v5_ordinal1(X2)
              & v1_funct_1(X2)
              & v5_relat_1(X2,X1)
              & v1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_ordinal1)).

fof(f16,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v5_ordinal1(sK2) ),
    inference(subsumption_resolution,[],[f15,f11])).

fof(f11,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f15,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v5_ordinal1(sK2) ),
    inference(subsumption_resolution,[],[f8,f9])).

fof(f9,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v5_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f20,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f19,f13])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | v5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f18,f9])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(sK0,X0)
      | v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f14,f10])).

fof(f10,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:48:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (24003)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.50  % (24002)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.50  % (24002)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f20,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ~v5_relat_1(sK2,sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f16,f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    v5_ordinal1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(X2) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) & v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f4])).
% 0.22/0.50  fof(f4,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((~v5_ordinal1(X2) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) & (v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v1_relat_1(X2))))),
% 0.22/0.50    inference(negated_conjecture,[],[f2])).
% 0.22/0.50  fof(f2,conjecture,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (v5_ordinal1(X2) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v1_relat_1(X2))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_ordinal1)).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ~v5_relat_1(sK2,sK1) | ~v5_ordinal1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f15,f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v5_ordinal1(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f8,f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v5_ordinal1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    v5_relat_1(sK2,sK1)),
% 0.22/0.50    inference(resolution,[],[f19,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(sK0,X0) | v5_relat_1(sK2,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f18,f9])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(sK2) | ~r1_tarski(sK0,X0) | v5_relat_1(sK2,X0)) )),
% 0.22/0.50    inference(resolution,[],[f14,f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    v5_relat_1(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | v5_relat_1(X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24002)------------------------------
% 0.22/0.50  % (24002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24002)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24002)Memory used [KB]: 5245
% 0.22/0.50  % (24002)Time elapsed: 0.091 s
% 0.22/0.50  % (24002)------------------------------
% 0.22/0.50  % (24002)------------------------------
% 0.22/0.50  % (23994)Success in time 0.142 s
%------------------------------------------------------------------------------
