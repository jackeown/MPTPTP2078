%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 (6258 expanded)
%              Number of leaves         :   14 (1287 expanded)
%              Depth                    :   45
%              Number of atoms          :  428 (19251 expanded)
%              Number of equality atoms :  122 (4195 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(subsumption_resolution,[],[f291,f39])).

fof(f39,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f291,plain,(
    sK0 = sK1 ),
    inference(forward_demodulation,[],[f279,f72])).

fof(f72,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f63,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f279,plain,(
    sK1 = k3_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f72,f259])).

fof(f259,plain,(
    k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(subsumption_resolution,[],[f258,f119])).

fof(f119,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(resolution,[],[f118,f38])).

fof(f38,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f76,f41])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),X0) ) ),
    inference(resolution,[],[f43,f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f258,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | k1_wellord2(sK0) = k1_wellord2(sK1)
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(superposition,[],[f246,f220])).

fof(f220,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(backward_demodulation,[],[f116,f218])).

fof(f218,plain,(
    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f217,f191])).

fof(f191,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1)) ),
    inference(resolution,[],[f185,f119])).

fof(f185,plain,(
    ! [X2] :
      ( ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(sK0))
      | r4_wellord1(k1_wellord2(sK1),k1_wellord2(X2)) ) ),
    inference(resolution,[],[f182,f118])).

fof(f182,plain,(
    ! [X0] :
      ( r4_wellord1(k1_wellord2(X0),k1_wellord2(sK1))
      | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK0)) ) ),
    inference(resolution,[],[f181,f38])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
      | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X0),k1_wellord2(X2)) ) ),
    inference(resolution,[],[f180,f41])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(k1_wellord2(X1),X0)
      | ~ r4_wellord1(X0,k1_wellord2(X2))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X2)) ) ),
    inference(resolution,[],[f169,f41])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,k1_wellord2(X2))
      | r4_wellord1(X1,k1_wellord2(X2)) ) ),
    inference(resolution,[],[f44,f41])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,X1)
      | ~ r4_wellord1(X1,X2)
      | r4_wellord1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

% (32281)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).

fof(f217,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1))
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1))
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f214,f155])).

fof(f155,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f145,f150])).

fof(f150,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f145,f116])).

fof(f145,plain,(
    ! [X0,X1] : k2_wellord1(k1_wellord2(X0),X1) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X0) ),
    inference(superposition,[],[f144,f77])).

fof(f77,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0) ),
    inference(resolution,[],[f55,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f144,plain,(
    ! [X2,X0,X1] : k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X2) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X2),X1) ),
    inference(resolution,[],[f62,f41])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f214,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f213,f210])).

fof(f210,plain,
    ( r2_hidden(sK0,sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f209,f40])).

fof(f40,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f209,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f205,f39])).

fof(f205,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f203,f121])).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | r2_hidden(X0,sK1)
      | sK1 = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f203,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f202,f158])).

fof(f158,plain,
    ( k1_wellord2(sK0) != k1_wellord2(sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(equality_factoring,[],[f150])).

fof(f202,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k1_wellord2(sK0) = k1_wellord2(sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f201,f38])).

fof(f201,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0)
    | k1_wellord2(sK0) = k1_wellord2(sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f197,f150])).

fof(f197,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f196,f40])).

fof(f196,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f168,f192])).

fof(f192,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f175,f191])).

fof(f175,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f174,f155])).

fof(f174,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f173,f130])).

fof(f130,plain,
    ( r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f129,f37])).

fof(f129,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f128,f40])).

fof(f128,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f124,f39])).

fof(f124,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f121,f112])).

fof(f112,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(sK0),X1) = X1 ) ),
    inference(resolution,[],[f46,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f173,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f172,f37])).

fof(f172,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f168,f132])).

fof(f132,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f131,f40])).

fof(f131,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f130,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(sK1),X0) = X0 ) ),
    inference(resolution,[],[f46,f37])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(forward_demodulation,[],[f167,f72])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f166,f41])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

% (32281)Refutation not found, incomplete strategy% (32281)------------------------------
% (32281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32281)Termination reason: Refutation not found, incomplete strategy

% (32281)Memory used [KB]: 10618
% (32281)Time elapsed: 0.092 s
% (32281)------------------------------
% (32281)------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f213,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f212,f37])).

fof(f212,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f168,f208])).

fof(f208,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f207,f40])).

fof(f207,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f204,f39])).

fof(f204,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f203,f127])).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | sK1 = X0
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(sK1),X0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | sK1 = X0
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(sK1),X0) = X0 ) ),
    inference(resolution,[],[f121,f111])).

fof(f116,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f106,f55])).

fof(f106,plain,
    ( r1_tarski(sK0,sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f105,f55])).

fof(f105,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f104,f40])).

fof(f104,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f103,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK1)
      | r1_tarski(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f58,f37])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f103,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f102,f40])).

fof(f102,plain,
    ( r1_tarski(sK1,sK0)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f95,f37])).

fof(f95,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f87,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r1_ordinal1(sK1,X0)
      | r1_ordinal1(X0,sK1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f56,f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f87,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(X1,sK0)
      | r1_tarski(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f58,f40])).

fof(f246,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(subsumption_resolution,[],[f245,f241])).

fof(f241,plain,
    ( r2_hidden(sK0,sK1)
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(subsumption_resolution,[],[f240,f40])).

fof(f240,plain,
    ( k1_wellord2(sK0) = k1_wellord2(sK1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f236,f39])).

fof(f236,plain,
    ( k1_wellord2(sK0) = k1_wellord2(sK1)
    | r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f226,f121])).

fof(f226,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(subsumption_resolution,[],[f225,f186])).

fof(f186,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK0)) ),
    inference(resolution,[],[f183,f38])).

fof(f183,plain,(
    ! [X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(sK1))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(sK0)) ) ),
    inference(resolution,[],[f181,f119])).

fof(f225,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK0))
    | k1_wellord2(sK0) = k1_wellord2(sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(forward_demodulation,[],[f224,f218])).

fof(f224,plain,
    ( k1_wellord2(sK0) = k1_wellord2(sK1)
    | ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f179,f218])).

fof(f179,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f178,f40])).

fof(f178,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f168,f177])).

fof(f177,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f176,f119])).

fof(f176,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f174,f116])).

fof(f245,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(subsumption_resolution,[],[f244,f37])).

fof(f244,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(superposition,[],[f168,f239])).

fof(f239,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | k1_wellord2(sK0) = k1_wellord2(sK1) ),
    inference(subsumption_resolution,[],[f238,f40])).

fof(f238,plain,
    ( k1_wellord2(sK0) = k1_wellord2(sK1)
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f235,f39])).

fof(f235,plain,
    ( k1_wellord2(sK0) = k1_wellord2(sK1)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f226,f127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:22:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (32291)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (32299)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (32299)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (32283)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f291,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    sK0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    sK0 = sK1),
% 0.21/0.50    inference(forward_demodulation,[],[f279,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.50    inference(equality_resolution,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    sK1 = k3_relat_1(k1_wellord2(sK0))),
% 0.21/0.50    inference(superposition,[],[f72,f259])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f258,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.50    inference(resolution,[],[f118,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))) )),
% 0.21/0.50    inference(resolution,[],[f76,f41])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X0,k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.50    inference(resolution,[],[f43,f41])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | r4_wellord1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f257])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | k1_wellord2(sK0) = k1_wellord2(sK1) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.50    inference(superposition,[],[f246,f220])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f116,f218])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f217,f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1))),
% 0.21/0.50    inference(resolution,[],[f185,f119])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X2] : (~r4_wellord1(k1_wellord2(X2),k1_wellord2(sK0)) | r4_wellord1(k1_wellord2(sK1),k1_wellord2(X2))) )),
% 0.21/0.50    inference(resolution,[],[f182,f118])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ( ! [X0] : (r4_wellord1(k1_wellord2(X0),k1_wellord2(sK1)) | ~r4_wellord1(k1_wellord2(X0),k1_wellord2(sK0))) )),
% 0.21/0.50    inference(resolution,[],[f181,f38])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r4_wellord1(k1_wellord2(X1),k1_wellord2(X2)) | ~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X0),k1_wellord2(X2))) )),
% 0.21/0.50    inference(resolution,[],[f180,f41])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(k1_wellord2(X1),X0) | ~r4_wellord1(X0,k1_wellord2(X2)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))) )),
% 0.21/0.50    inference(resolution,[],[f169,f41])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r4_wellord1(X1,X0) | ~r4_wellord1(X0,k1_wellord2(X2)) | r4_wellord1(X1,k1_wellord2(X2))) )),
% 0.21/0.50    inference(resolution,[],[f44,f41])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | ~r4_wellord1(X1,X2) | r4_wellord1(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  % (32281)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r4_wellord1(X0,X2) | (~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1)) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f215])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1)) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.50    inference(superposition,[],[f214,f155])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.50    inference(superposition,[],[f145,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.50    inference(superposition,[],[f145,f116])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X0),X1) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X0)) )),
% 0.21/0.50    inference(superposition,[],[f144,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f55,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X2) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X2),X1)) )),
% 0.21/0.50    inference(resolution,[],[f62,f41])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f213,f210])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    r2_hidden(sK0,sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f209,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    v3_ordinal1(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f205,f39])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) | r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.21/0.50    inference(resolution,[],[f203,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK1,X0) | r2_hidden(X0,sK1) | sK1 = X0 | ~v3_ordinal1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f47,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    v3_ordinal1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    ~r2_hidden(sK1,sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f202,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    k1_wellord2(sK0) != k1_wellord2(sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(equality_factoring,[],[f150])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ~r2_hidden(sK1,sK0) | k1_wellord2(sK0) = k1_wellord2(sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f201,f38])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0) | k1_wellord2(sK0) = k1_wellord2(sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(superposition,[],[f197,f150])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f196,f40])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(superposition,[],[f168,f192])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f175,f191])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(superposition,[],[f174,f155])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f173,f130])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f37])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f128,f40])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f124,f39])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(resolution,[],[f121,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(sK0),X1) = X1) )),
% 0.21/0.51    inference(resolution,[],[f46,f40])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f172,f37])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(superposition,[],[f168,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f131,f40])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    inference(resolution,[],[f130,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0) )),
% 0.21/0.51    inference(resolution,[],[f46,f37])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f167,f72])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f166,f41])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),k1_wellord1(k1_wellord2(X0),X1))) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f42,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  % (32281)Refutation not found, incomplete strategy% (32281)------------------------------
% 0.21/0.51  % (32281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32281)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32281)Memory used [KB]: 10618
% 0.21/0.51  % (32281)Time elapsed: 0.092 s
% 0.21/0.51  % (32281)------------------------------
% 0.21/0.51  % (32281)------------------------------
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f212,f37])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(superposition,[],[f168,f208])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f207,f40])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f204,f39])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    inference(resolution,[],[f203,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0) )),
% 0.21/0.51    inference(resolution,[],[f121,f111])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(resolution,[],[f106,f55])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(resolution,[],[f105,f55])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f40])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.51    inference(resolution,[],[f103,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_ordinal1(X0,sK1) | r1_tarski(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f58,f37])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f40])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f37])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1) | r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.51    inference(resolution,[],[f87,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (r1_ordinal1(sK1,X0) | r1_ordinal1(X0,sK1) | ~v3_ordinal1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f56,f37])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X1] : (~r1_ordinal1(X1,sK0) | r1_tarski(X1,sK0) | ~v3_ordinal1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f58,f40])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f245,f241])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f240,f40])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k1_wellord2(sK1) | r2_hidden(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f236,f39])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k1_wellord2(sK1) | r2_hidden(sK0,sK1) | sK0 = sK1 | ~v3_ordinal1(sK0)),
% 0.21/0.51    inference(resolution,[],[f226,f121])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    ~r2_hidden(sK1,sK0) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f225,f186])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK0))),
% 0.21/0.51    inference(resolution,[],[f183,f38])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ( ! [X1] : (~r4_wellord1(k1_wellord2(X1),k1_wellord2(sK1)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(sK0))) )),
% 0.21/0.51    inference(resolution,[],[f181,f119])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK0)) | k1_wellord2(sK0) = k1_wellord2(sK1) | ~r2_hidden(sK1,sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f224,f218])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k1_wellord2(sK1) | ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f179,f218])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f178,f40])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(superposition,[],[f168,f177])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f176,f119])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    inference(superposition,[],[f174,f116])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f244,f37])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.51    inference(superposition,[],[f168,f239])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | k1_wellord2(sK0) = k1_wellord2(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f238,f40])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k1_wellord2(sK1) | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f235,f39])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k1_wellord2(sK1) | sK0 = sK1 | ~v3_ordinal1(sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    inference(resolution,[],[f226,f127])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (32299)------------------------------
% 0.21/0.51  % (32299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32299)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (32299)Memory used [KB]: 1791
% 0.21/0.51  % (32299)Time elapsed: 0.082 s
% 0.21/0.51  % (32299)------------------------------
% 0.21/0.51  % (32299)------------------------------
% 0.21/0.51  % (32279)Success in time 0.147 s
%------------------------------------------------------------------------------
