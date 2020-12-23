%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  91 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   15
%              Number of atoms          :  196 ( 642 expanded)
%              Number of equality atoms :   69 ( 248 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(subsumption_resolution,[],[f84,f19])).

fof(f19,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f84,plain,(
    sK1 != k5_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f82,f47])).

fof(f47,plain,(
    sK1 = k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f44,f15])).

fof(f15,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    k5_relat_1(sK2,sK1) != k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f14,f13,f41,f20,f16,f17,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | k5_relat_1(X1,sK1) != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = X1 ) ),
    inference(forward_demodulation,[],[f80,f25])).

fof(f25,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(X1)
      | k5_relat_1(X1,sK1) != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f79,f24])).

fof(f24,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(X1)
      | k5_relat_1(X1,sK1) != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f78,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(X1)
      | k5_relat_1(X1,sK1) != k5_relat_1(k6_relat_1(X0),sK1)
      | k6_relat_1(X0) = X1 ) ),
    inference(superposition,[],[f73,f26])).

fof(f26,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),sK0)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f72,f18])).

fof(f18,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f71,f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_relat_1(sK1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f65,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k2_relat_1(X1),sK0)
      | ~ v1_relat_1(sK1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f35,f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X1) != k1_relat_1(X2)
      | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(f17,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    sK2 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
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

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:52:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (22622)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.48  % (22606)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.49  % (22606)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f84,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    sK1 = k5_relat_1(sK2,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    sK1 != k5_relat_1(sK2,sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f82,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    sK1 = k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f44,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f21,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    k5_relat_1(sK2,sK1) != k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f14,f13,f41,f20,f16,f17,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),sK0) | ~r1_tarski(X0,sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | k5_relat_1(X1,sK1) != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = X1) )),
% 0.22/0.49    inference(forward_demodulation,[],[f80,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),sK0) | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(X1) | k5_relat_1(X1,sK1) != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = X1) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f79,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),sK0) | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(X1) | k5_relat_1(X1,sK1) != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = X1) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f78,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),sK0) | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(X1) | k5_relat_1(X1,sK1) != k5_relat_1(k6_relat_1(X0),sK1) | k6_relat_1(X0) = X1) )),
% 0.22/0.49    inference(superposition,[],[f73,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k2_relat_1(X0),sK0) | k1_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1) | X0 = X1) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f72,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    v2_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k2_relat_1(X1),sK0) | k1_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f71,f21])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),sK0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k2_relat_1(X1),sK0) | ~v1_relat_1(sK1) | k1_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f65,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r1_tarski(k2_relat_1(X1),sK0) | ~v1_relat_1(sK1) | k1_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X1,sK1) != k5_relat_1(X0,sK1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.22/0.49    inference(superposition,[],[f35,f15])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(X1) != k1_relat_1(X2) | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK2),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    sK2 != k6_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (22606)------------------------------
% 0.22/0.49  % (22606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22606)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (22606)Memory used [KB]: 1663
% 0.22/0.49  % (22606)Time elapsed: 0.052 s
% 0.22/0.49  % (22606)------------------------------
% 0.22/0.49  % (22606)------------------------------
% 0.22/0.49  % (22598)Success in time 0.12 s
%------------------------------------------------------------------------------
