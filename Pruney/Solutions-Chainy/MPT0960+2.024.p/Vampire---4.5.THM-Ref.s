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
% DateTime   : Thu Dec  3 13:00:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 256 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   24
%              Number of atoms          :  330 (1000 expanded)
%              Number of equality atoms :   63 ( 193 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f567,plain,(
    $false ),
    inference(resolution,[],[f566,f45])).

fof(f45,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f34])).

fof(f34,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

fof(f566,plain,(
    ! [X13] : r1_tarski(k1_wellord2(X13),k2_zfmisc_1(X13,X13)) ),
    inference(forward_demodulation,[],[f565,f509])).

fof(f509,plain,(
    ! [X2] : k2_relat_1(k1_wellord2(X2)) = X2 ),
    inference(subsumption_resolution,[],[f504,f199])).

fof(f199,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) ),
    inference(superposition,[],[f196,f87])).

fof(f87,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0) ),
    inference(forward_demodulation,[],[f84,f83])).

fof(f83,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f46,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f46,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f84,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f50,f46])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(f196,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_wellord1(k1_wellord2(X0),X1)),X1) ),
    inference(subsumption_resolution,[],[f195,f46])).

fof(f195,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k2_wellord1(k1_wellord2(X0),X1)),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f117,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k1_wellord2(X1),X0))
      | r1_tarski(k2_relat_1(k2_wellord1(k1_wellord2(X1),X0)),X0) ) ),
    inference(superposition,[],[f56,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_wellord1(k1_wellord2(X0),X1) = k8_relat_1(X1,k7_relat_1(k1_wellord2(X0),X1)) ),
    inference(resolution,[],[f57,f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f504,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(k1_wellord2(X2)),X2)
      | k2_relat_1(k1_wellord2(X2)) = X2 ) ),
    inference(resolution,[],[f500,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f500,plain,(
    ! [X2] : r1_tarski(X2,k2_relat_1(k1_wellord2(X2))) ),
    inference(subsumption_resolution,[],[f496,f46])).

fof(f496,plain,(
    ! [X2] :
      ( r1_tarski(X2,k2_relat_1(k1_wellord2(X2)))
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(resolution,[],[f493,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f164,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f164,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f53,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f493,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f492,f46])).

fof(f492,plain,(
    ! [X0] :
      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,(
    ! [X0] :
      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f490,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1)
        & r2_hidden(sK1(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

fof(f490,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f489,f46])).

fof(f489,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f488,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f488,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | ~ r1_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1)))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(duplicate_literal_removal,[],[f487])).

fof(f487,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | ~ r1_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1)))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X0)
      | ~ r1_tarski(X4,X5) ) ),
    inference(global_subsumption,[],[f46,f76])).

fof(f76,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f565,plain,(
    ! [X13] : r1_tarski(k1_wellord2(X13),k2_zfmisc_1(X13,k2_relat_1(k1_wellord2(X13)))) ),
    inference(subsumption_resolution,[],[f560,f46])).

fof(f560,plain,(
    ! [X13] :
      ( r1_tarski(k1_wellord2(X13),k2_zfmisc_1(X13,k2_relat_1(k1_wellord2(X13))))
      | ~ v1_relat_1(k1_wellord2(X13)) ) ),
    inference(superposition,[],[f51,f517])).

fof(f517,plain,(
    ! [X2] : k1_relat_1(k1_wellord2(X2)) = X2 ),
    inference(subsumption_resolution,[],[f512,f213])).

fof(f213,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k1_wellord2(X1)),X1) ),
    inference(subsumption_resolution,[],[f210,f46])).

fof(f210,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k1_wellord2(X1)),X1)
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(superposition,[],[f55,f208])).

fof(f208,plain,(
    ! [X1] : k1_wellord2(X1) = k7_relat_1(k1_wellord2(X1),X1) ),
    inference(forward_demodulation,[],[f204,f87])).

fof(f204,plain,(
    ! [X1] : k2_wellord1(k1_wellord2(X1),X1) = k7_relat_1(k1_wellord2(X1),X1) ),
    inference(superposition,[],[f102,f200])).

fof(f200,plain,(
    ! [X0] : k1_wellord2(X0) = k8_relat_1(X0,k1_wellord2(X0)) ),
    inference(resolution,[],[f199,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k1_wellord2(X0)),X1)
      | k1_wellord2(X0) = k8_relat_1(X1,k1_wellord2(X0)) ) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f102,plain,(
    ! [X0,X1] : k2_wellord1(k1_wellord2(X0),X1) = k7_relat_1(k8_relat_1(X1,k1_wellord2(X0)),X1) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

% (9869)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f512,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(k1_wellord2(X2)),X2)
      | k1_relat_1(k1_wellord2(X2)) = X2 ) ),
    inference(resolution,[],[f501,f71])).

fof(f501,plain,(
    ! [X3] : r1_tarski(X3,k1_relat_1(k1_wellord2(X3))) ),
    inference(subsumption_resolution,[],[f497,f46])).

fof(f497,plain,(
    ! [X3] :
      ( r1_tarski(X3,k1_relat_1(k1_wellord2(X3)))
      | ~ v1_relat_1(k1_wellord2(X3)) ) ),
    inference(resolution,[],[f493,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f143,f47])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(X1))
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:48:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (9850)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (9850)Refutation not found, incomplete strategy% (9850)------------------------------
% 0.22/0.50  % (9850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9850)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (9850)Memory used [KB]: 6140
% 0.22/0.50  % (9850)Time elapsed: 0.091 s
% 0.22/0.50  % (9850)------------------------------
% 0.22/0.50  % (9850)------------------------------
% 0.22/0.50  % (9845)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (9858)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (9844)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (9868)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (9860)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (9853)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (9849)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (9856)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (9847)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (9852)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (9862)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (9845)Refutation not found, incomplete strategy% (9845)------------------------------
% 0.22/0.52  % (9845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9845)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9845)Memory used [KB]: 10618
% 0.22/0.52  % (9845)Time elapsed: 0.102 s
% 0.22/0.52  % (9845)------------------------------
% 0.22/0.52  % (9845)------------------------------
% 0.22/0.52  % (9870)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (9866)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (9851)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (9851)Refutation not found, incomplete strategy% (9851)------------------------------
% 0.22/0.52  % (9851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9851)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9851)Memory used [KB]: 10618
% 0.22/0.52  % (9851)Time elapsed: 0.114 s
% 0.22/0.52  % (9851)------------------------------
% 0.22/0.52  % (9851)------------------------------
% 0.22/0.53  % (9867)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (9856)Refutation not found, incomplete strategy% (9856)------------------------------
% 0.22/0.53  % (9856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9856)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9856)Memory used [KB]: 10490
% 0.22/0.53  % (9856)Time elapsed: 0.113 s
% 0.22/0.53  % (9856)------------------------------
% 0.22/0.53  % (9856)------------------------------
% 0.22/0.53  % (9861)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (9859)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (9863)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (9865)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (9854)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (9846)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (9858)Refutation not found, incomplete strategy% (9858)------------------------------
% 0.22/0.53  % (9858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9858)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9858)Memory used [KB]: 6012
% 0.22/0.53  % (9858)Time elapsed: 0.126 s
% 0.22/0.53  % (9858)------------------------------
% 0.22/0.53  % (9858)------------------------------
% 0.22/0.54  % (9864)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (9857)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (9855)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (9866)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f567,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(resolution,[],[f566,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
% 0.22/0.55  fof(f566,plain,(
% 0.22/0.55    ( ! [X13] : (r1_tarski(k1_wellord2(X13),k2_zfmisc_1(X13,X13))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f565,f509])).
% 0.22/0.55  fof(f509,plain,(
% 0.22/0.55    ( ! [X2] : (k2_relat_1(k1_wellord2(X2)) = X2) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f504,f199])).
% 0.22/0.55  fof(f199,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(k1_wellord2(X0)),X0)) )),
% 0.22/0.55    inference(superposition,[],[f196,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f84,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.55    inference(global_subsumption,[],[f46,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.55    inference(equality_resolution,[],[f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(rectify,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0)))) )),
% 0.22/0.55    inference(resolution,[],[f50,f46])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_wellord1(X0,k3_relat_1(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 1.52/0.55  fof(f19,plain,(
% 1.52/0.55    ! [X0] : (k2_wellord1(X0,k3_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.52/0.55    inference(ennf_transformation,[],[f13])).
% 1.52/0.55  fof(f13,axiom,(
% 1.52/0.55    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).
% 1.52/0.55  fof(f196,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_wellord1(k1_wellord2(X0),X1)),X1)) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f195,f46])).
% 1.52/0.55  fof(f195,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_wellord1(k1_wellord2(X0),X1)),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.52/0.55    inference(resolution,[],[f117,f54])).
% 1.52/0.55  fof(f54,plain,(
% 1.52/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f23])).
% 1.52/0.55  fof(f23,plain,(
% 1.52/0.55    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.52/0.55    inference(ennf_transformation,[],[f3])).
% 1.52/0.55  fof(f3,axiom,(
% 1.52/0.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.52/0.55  fof(f117,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(k1_wellord2(X1),X0)) | r1_tarski(k2_relat_1(k2_wellord1(k1_wellord2(X1),X0)),X0)) )),
% 1.52/0.55    inference(superposition,[],[f56,f99])).
% 1.52/0.55  fof(f99,plain,(
% 1.52/0.55    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X0),X1) = k8_relat_1(X1,k7_relat_1(k1_wellord2(X0),X1))) )),
% 1.52/0.55    inference(resolution,[],[f57,f46])).
% 1.52/0.55  fof(f57,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 1.52/0.55    inference(cnf_transformation,[],[f26])).
% 1.52/0.55  fof(f26,plain,(
% 1.52/0.55    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(ennf_transformation,[],[f12])).
% 1.52/0.55  fof(f12,axiom,(
% 1.52/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 1.52/0.55  fof(f56,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f25])).
% 1.52/0.55  fof(f25,plain,(
% 1.52/0.55    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(ennf_transformation,[],[f4])).
% 1.52/0.55  fof(f4,axiom,(
% 1.52/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 1.52/0.55  fof(f504,plain,(
% 1.52/0.55    ( ! [X2] : (~r1_tarski(k2_relat_1(k1_wellord2(X2)),X2) | k2_relat_1(k1_wellord2(X2)) = X2) )),
% 1.52/0.55    inference(resolution,[],[f500,f71])).
% 1.52/0.55  fof(f71,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.52/0.55    inference(cnf_transformation,[],[f44])).
% 1.52/0.55  fof(f44,plain,(
% 1.52/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.55    inference(flattening,[],[f43])).
% 1.52/0.55  fof(f43,plain,(
% 1.52/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.55    inference(nnf_transformation,[],[f1])).
% 1.52/0.55  fof(f1,axiom,(
% 1.52/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.55  fof(f500,plain,(
% 1.52/0.55    ( ! [X2] : (r1_tarski(X2,k2_relat_1(k1_wellord2(X2)))) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f496,f46])).
% 1.52/0.55  fof(f496,plain,(
% 1.52/0.55    ( ! [X2] : (r1_tarski(X2,k2_relat_1(k1_wellord2(X2))) | ~v1_relat_1(k1_wellord2(X2))) )),
% 1.52/0.55    inference(resolution,[],[f493,f166])).
% 1.52/0.55  fof(f166,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f164,f47])).
% 1.52/0.55  fof(f47,plain,(
% 1.52/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.52/0.55    inference(cnf_transformation,[],[f2])).
% 1.52/0.55  fof(f2,axiom,(
% 1.52/0.55    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.52/0.55  fof(f164,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.52/0.55    inference(superposition,[],[f53,f49])).
% 1.52/0.55  fof(f49,plain,(
% 1.52/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.52/0.55    inference(cnf_transformation,[],[f8])).
% 1.52/0.55  fof(f8,axiom,(
% 1.52/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.52/0.55  fof(f53,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f22])).
% 1.52/0.55  fof(f22,plain,(
% 1.52/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.55    inference(flattening,[],[f21])).
% 1.52/0.55  fof(f21,plain,(
% 1.52/0.55    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.55    inference(ennf_transformation,[],[f7])).
% 1.52/0.55  fof(f7,axiom,(
% 1.52/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.52/0.55  fof(f493,plain,(
% 1.52/0.55    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0))) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f492,f46])).
% 1.52/0.55  fof(f492,plain,(
% 1.52/0.55    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.52/0.55    inference(duplicate_literal_removal,[],[f491])).
% 1.52/0.55  fof(f491,plain,(
% 1.52/0.55    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.52/0.55    inference(resolution,[],[f490,f60])).
% 1.52/0.55  fof(f60,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f37])).
% 1.52/0.55  fof(f37,plain,(
% 1.52/0.55    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) & r2_hidden(sK1(X0,X1),X0)) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f36])).
% 1.52/0.55  fof(f36,plain,(
% 1.52/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.52/0.55    introduced(choice_axiom,[])).
% 1.52/0.55  fof(f31,plain,(
% 1.52/0.55    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(flattening,[],[f30])).
% 1.52/0.55  fof(f30,plain,(
% 1.52/0.55    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(ennf_transformation,[],[f9])).
% 1.52/0.55  fof(f9,axiom,(
% 1.52/0.55    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).
% 1.52/0.55  fof(f490,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f489,f46])).
% 1.52/0.55  fof(f489,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f488,f79])).
% 1.52/0.55  fof(f79,plain,(
% 1.52/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.55    inference(equality_resolution,[],[f70])).
% 1.52/0.55  fof(f70,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.52/0.55    inference(cnf_transformation,[],[f44])).
% 1.52/0.55  fof(f488,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | ~r1_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1))) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 1.52/0.55    inference(duplicate_literal_removal,[],[f487])).
% 1.52/0.55  fof(f487,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | ~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | ~r1_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1))) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 1.52/0.55    inference(resolution,[],[f81,f61])).
% 1.52/0.55  fof(f61,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f37])).
% 1.52/0.55  fof(f81,plain,(
% 1.52/0.55    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X4,X0) | ~r2_hidden(X5,X0) | ~r1_tarski(X4,X5)) )),
% 1.52/0.55    inference(global_subsumption,[],[f46,f76])).
% 1.52/0.55  fof(f76,plain,(
% 1.52/0.55    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.52/0.55    inference(equality_resolution,[],[f64])).
% 1.52/0.55  fof(f64,plain,(
% 1.52/0.55    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f42])).
% 1.52/0.55  fof(f565,plain,(
% 1.52/0.55    ( ! [X13] : (r1_tarski(k1_wellord2(X13),k2_zfmisc_1(X13,k2_relat_1(k1_wellord2(X13))))) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f560,f46])).
% 1.52/0.55  fof(f560,plain,(
% 1.52/0.55    ( ! [X13] : (r1_tarski(k1_wellord2(X13),k2_zfmisc_1(X13,k2_relat_1(k1_wellord2(X13)))) | ~v1_relat_1(k1_wellord2(X13))) )),
% 1.52/0.55    inference(superposition,[],[f51,f517])).
% 1.52/0.55  fof(f517,plain,(
% 1.52/0.55    ( ! [X2] : (k1_relat_1(k1_wellord2(X2)) = X2) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f512,f213])).
% 1.52/0.55  fof(f213,plain,(
% 1.52/0.55    ( ! [X1] : (r1_tarski(k1_relat_1(k1_wellord2(X1)),X1)) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f210,f46])).
% 1.52/0.55  fof(f210,plain,(
% 1.52/0.55    ( ! [X1] : (r1_tarski(k1_relat_1(k1_wellord2(X1)),X1) | ~v1_relat_1(k1_wellord2(X1))) )),
% 1.52/0.55    inference(superposition,[],[f55,f208])).
% 1.52/0.55  fof(f208,plain,(
% 1.52/0.55    ( ! [X1] : (k1_wellord2(X1) = k7_relat_1(k1_wellord2(X1),X1)) )),
% 1.52/0.55    inference(forward_demodulation,[],[f204,f87])).
% 1.52/0.55  fof(f204,plain,(
% 1.52/0.55    ( ! [X1] : (k2_wellord1(k1_wellord2(X1),X1) = k7_relat_1(k1_wellord2(X1),X1)) )),
% 1.52/0.55    inference(superposition,[],[f102,f200])).
% 1.52/0.55  fof(f200,plain,(
% 1.52/0.55    ( ! [X0] : (k1_wellord2(X0) = k8_relat_1(X0,k1_wellord2(X0))) )),
% 1.52/0.55    inference(resolution,[],[f199,f105])).
% 1.52/0.55  fof(f105,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k1_wellord2(X0)),X1) | k1_wellord2(X0) = k8_relat_1(X1,k1_wellord2(X0))) )),
% 1.52/0.55    inference(resolution,[],[f59,f46])).
% 1.52/0.55  fof(f59,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 1.52/0.55    inference(cnf_transformation,[],[f29])).
% 1.52/0.55  fof(f29,plain,(
% 1.52/0.55    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(flattening,[],[f28])).
% 1.52/0.55  fof(f28,plain,(
% 1.52/0.55    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(ennf_transformation,[],[f5])).
% 1.52/0.55  fof(f5,axiom,(
% 1.52/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.52/0.55  fof(f102,plain,(
% 1.52/0.55    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X0),X1) = k7_relat_1(k8_relat_1(X1,k1_wellord2(X0)),X1)) )),
% 1.52/0.55    inference(resolution,[],[f58,f46])).
% 1.52/0.55  fof(f58,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f27])).
% 1.52/0.55  fof(f27,plain,(
% 1.52/0.55    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(ennf_transformation,[],[f11])).
% 1.52/0.55  fof(f11,axiom,(
% 1.52/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).
% 1.52/0.55  % (9869)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.52/0.55  fof(f55,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f24])).
% 1.52/0.55  fof(f24,plain,(
% 1.52/0.55    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.52/0.55    inference(ennf_transformation,[],[f10])).
% 1.52/0.55  fof(f10,axiom,(
% 1.52/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.52/0.55  fof(f512,plain,(
% 1.52/0.55    ( ! [X2] : (~r1_tarski(k1_relat_1(k1_wellord2(X2)),X2) | k1_relat_1(k1_wellord2(X2)) = X2) )),
% 1.52/0.55    inference(resolution,[],[f501,f71])).
% 1.52/0.55  fof(f501,plain,(
% 1.52/0.55    ( ! [X3] : (r1_tarski(X3,k1_relat_1(k1_wellord2(X3)))) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f497,f46])).
% 1.52/0.55  fof(f497,plain,(
% 1.52/0.55    ( ! [X3] : (r1_tarski(X3,k1_relat_1(k1_wellord2(X3))) | ~v1_relat_1(k1_wellord2(X3))) )),
% 1.52/0.55    inference(resolution,[],[f493,f145])).
% 1.52/0.55  fof(f145,plain,(
% 1.52/0.55    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.52/0.55    inference(subsumption_resolution,[],[f143,f47])).
% 1.52/0.55  fof(f143,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.52/0.55    inference(superposition,[],[f52,f48])).
% 1.52/0.55  fof(f48,plain,(
% 1.52/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.52/0.55    inference(cnf_transformation,[],[f8])).
% 1.52/0.55  fof(f52,plain,(
% 1.52/0.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f22])).
% 1.52/0.55  fof(f51,plain,(
% 1.52/0.55    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.52/0.55    inference(cnf_transformation,[],[f20])).
% 1.52/0.55  fof(f20,plain,(
% 1.52/0.55    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.55    inference(ennf_transformation,[],[f6])).
% 1.52/0.55  fof(f6,axiom,(
% 1.52/0.55    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.52/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.52/0.55  % SZS output end Proof for theBenchmark
% 1.52/0.55  % (9866)------------------------------
% 1.52/0.55  % (9866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (9866)Termination reason: Refutation
% 1.52/0.55  
% 1.52/0.55  % (9866)Memory used [KB]: 6652
% 1.52/0.55  % (9866)Time elapsed: 0.130 s
% 1.52/0.55  % (9866)------------------------------
% 1.52/0.55  % (9866)------------------------------
% 1.52/0.56  % (9841)Success in time 0.192 s
%------------------------------------------------------------------------------
