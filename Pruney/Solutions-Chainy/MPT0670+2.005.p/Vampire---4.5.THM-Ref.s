%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 102 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 ( 416 expanded)
%              Number of equality atoms :   64 ( 113 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f203,plain,(
    $false ),
    inference(subsumption_resolution,[],[f202,f29])).

fof(f29,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)
    & r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
        & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)
      & r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
         => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(f202,plain,(
    k1_funct_1(sK2,sK0) = k1_funct_1(k8_relat_1(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f197,f86])).

fof(f86,plain,(
    k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f85,f30])).

fof(f30,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f85,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f84,f31])).

fof(f31,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f84,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(resolution,[],[f74,f43])).

fof(f43,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k6_relat_1(X0),X3) = X3
      | ~ r2_hidden(X3,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X1,X3) = X3
      | ~ r2_hidden(X3,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f74,plain,(
    r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(subsumption_resolution,[],[f73,f26])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f68,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f28,plain,(
    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f197,plain,(
    k1_funct_1(k8_relat_1(sK1,sK2),sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0)) ),
    inference(resolution,[],[f94,f28])).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2)))
      | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2) ) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2)))
      | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f92,f31])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2)))
      | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f91,f26])).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2)))
      | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f89,f27])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2)))
      | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f37,f45])).

fof(f45,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
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
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:21:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (27179)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.43  % (27179)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.44  % (27186)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f203,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f202,f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) & r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) & r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.44    inference(flattening,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.20/0.44    inference(negated_conjecture,[],[f6])).
% 0.20/0.44  fof(f6,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).
% 0.20/0.44  fof(f202,plain,(
% 0.20/0.44    k1_funct_1(sK2,sK0) = k1_funct_1(k8_relat_1(sK1,sK2),sK0)),
% 0.20/0.44    inference(forward_demodulation,[],[f197,f86])).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f85,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.20/0.44    inference(subsumption_resolution,[],[f84,f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    k1_funct_1(sK2,sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.20/0.44    inference(resolution,[],[f74,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0,X3] : (k1_funct_1(k6_relat_1(X0),X3) = X3 | ~r2_hidden(X3,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(equality_resolution,[],[f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0,X3,X1] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0) | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(rectify,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(nnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f73,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    v1_relat_1(sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 0.20/0.44    inference(subsumption_resolution,[],[f68,f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    v1_funct_1(sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.44    inference(resolution,[],[f28,f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.44    inference(flattening,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.44    inference(nnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f197,plain,(
% 0.20/0.44    k1_funct_1(k8_relat_1(sK1,sK2),sK0) = k1_funct_1(k6_relat_1(sK1),k1_funct_1(sK2,sK0))),
% 0.20/0.44    inference(resolution,[],[f94,f28])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    ( ! [X2,X1] : (~r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2))) | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f93,f30])).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    ( ! [X2,X1] : (~r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2))) | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f92,f31])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    ( ! [X2,X1] : (~r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2))) | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f91,f26])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    ( ! [X2,X1] : (~r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2))) | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f89,f27])).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    ( ! [X2,X1] : (~r2_hidden(X2,k1_relat_1(k8_relat_1(X1,sK2))) | k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) = k1_funct_1(k8_relat_1(X1,sK2),X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.44    inference(superposition,[],[f37,f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 0.20/0.44    inference(resolution,[],[f26,f32])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (27179)------------------------------
% 0.20/0.44  % (27179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (27179)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (27179)Memory used [KB]: 1791
% 0.20/0.44  % (27179)Time elapsed: 0.042 s
% 0.20/0.44  % (27179)------------------------------
% 0.20/0.44  % (27179)------------------------------
% 0.20/0.44  % (27174)Success in time 0.08 s
%------------------------------------------------------------------------------
