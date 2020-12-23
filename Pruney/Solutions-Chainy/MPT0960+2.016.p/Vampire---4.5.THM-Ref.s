%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:08 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 223 expanded)
%              Number of leaves         :   21 (  57 expanded)
%              Depth                    :   24
%              Number of atoms          :  341 ( 874 expanded)
%              Number of equality atoms :   62 ( 158 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f316])).

fof(f316,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f86,f288])).

fof(f288,plain,(
    ! [X6] : r1_tarski(k1_wellord2(X6),k2_zfmisc_1(X6,X6)) ),
    inference(backward_demodulation,[],[f190,f285])).

fof(f285,plain,(
    ! [X0] : k2_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f284,f213])).

fof(f213,plain,(
    ! [X0] : r1_tarski(X0,k2_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f148,f168])).

fof(f168,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f167,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f167,plain,(
    ! [X0] :
      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f141,f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f140,f46])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f139,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1)))
      | ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1)))
      | ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | ~ r2_hidden(sK1(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(resolution,[],[f133,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f133,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | r1_tarski(X0,k2_relat_1(k1_wellord2(X1))) ) ),
    inference(resolution,[],[f125,f46])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k2_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f123,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f284,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(k1_wellord2(X0)))
      | k2_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(superposition,[],[f197,f265])).

fof(f265,plain,(
    ! [X0] : k1_wellord2(X0) = k8_relat_1(X0,k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f263,f46])).

fof(f263,plain,(
    ! [X0] :
      ( k1_wellord2(X0) = k8_relat_1(X0,k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f260,f102])).

fof(f102,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k8_relat_1(X7,X6))
      | k8_relat_1(X7,X6) = X6
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f73,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f260,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k8_relat_1(X0,k1_wellord2(X0))) ),
    inference(superposition,[],[f258,f116])).

fof(f116,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0) ),
    inference(forward_demodulation,[],[f88,f91])).

fof(f91,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f80,f46])).

fof(f80,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f51,f46])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(f258,plain,(
    ! [X0,X1] : r1_tarski(k2_wellord1(k1_wellord2(X0),X1),k8_relat_1(X1,k1_wellord2(X0))) ),
    inference(subsumption_resolution,[],[f257,f46])).

fof(f257,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_wellord1(k1_wellord2(X0),X1),k8_relat_1(X1,k1_wellord2(X0)))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f160,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,k1_wellord2(X1)))
      | r1_tarski(k2_wellord1(k1_wellord2(X1),X0),k8_relat_1(X0,k1_wellord2(X1))) ) ),
    inference(superposition,[],[f58,f112])).

fof(f112,plain,(
    ! [X0,X1] : k2_wellord1(k1_wellord2(X0),X1) = k7_relat_1(k8_relat_1(X1,k1_wellord2(X0)),X1) ),
    inference(resolution,[],[f61,f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(k8_relat_1(X0,k1_wellord2(X1))))
      | k2_relat_1(k8_relat_1(X0,k1_wellord2(X1))) = X0 ) ),
    inference(resolution,[],[f101,f46])).

fof(f101,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | k2_relat_1(k8_relat_1(X4,X5)) = X4
      | ~ r1_tarski(X4,k2_relat_1(k8_relat_1(X4,X5))) ) ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f190,plain,(
    ! [X6] : r1_tarski(k1_wellord2(X6),k2_zfmisc_1(X6,k2_relat_1(k1_wellord2(X6)))) ),
    inference(subsumption_resolution,[],[f186,f46])).

fof(f186,plain,(
    ! [X6] :
      ( r1_tarski(k1_wellord2(X6),k2_zfmisc_1(X6,k2_relat_1(k1_wellord2(X6))))
      | ~ v1_relat_1(k1_wellord2(X6)) ) ),
    inference(superposition,[],[f52,f173])).

fof(f173,plain,(
    ! [X0] : k1_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f169,f132])).

fof(f132,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k1_wellord2(X1)))
      | k1_relat_1(k1_wellord2(X1)) = X1 ) ),
    inference(superposition,[],[f99,f108])).

fof(f108,plain,(
    ! [X0] : k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
    inference(forward_demodulation,[],[f105,f91])).

fof(f105,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f53,f46])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f99,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f169,plain,(
    ! [X0] : r1_tarski(X0,k1_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f168,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | r1_tarski(X0,k1_relat_1(k1_wellord2(X1))) ) ),
    inference(resolution,[],[f120,f46])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f118,f47])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(X1))
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f54,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f86,plain,
    ( ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_1
  <=> r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f87,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f34])).

fof(f34,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:34:47 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.43  % (19267)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.43  % (19267)Refutation not found, incomplete strategy% (19267)------------------------------
% 0.19/0.43  % (19267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (19267)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (19267)Memory used [KB]: 10490
% 0.19/0.45  % (19267)Time elapsed: 0.062 s
% 0.19/0.45  % (19267)------------------------------
% 0.19/0.45  % (19267)------------------------------
% 0.19/0.47  % (19264)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.47  % (19258)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.49  % (19280)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.49  % (19259)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.51  % (19274)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.51  % (19271)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.51  % (19256)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  % (19256)Refutation not found, incomplete strategy% (19256)------------------------------
% 0.19/0.51  % (19256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (19256)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (19256)Memory used [KB]: 10490
% 0.19/0.51  % (19256)Time elapsed: 0.119 s
% 0.19/0.51  % (19256)------------------------------
% 0.19/0.51  % (19256)------------------------------
% 0.19/0.52  % (19266)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.52  % (19258)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f317,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f87,f316])).
% 0.19/0.52  fof(f316,plain,(
% 0.19/0.52    spl4_1),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f312])).
% 0.19/0.52  fof(f312,plain,(
% 0.19/0.52    $false | spl4_1),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f86,f288])).
% 0.19/0.52  fof(f288,plain,(
% 0.19/0.52    ( ! [X6] : (r1_tarski(k1_wellord2(X6),k2_zfmisc_1(X6,X6))) )),
% 0.19/0.52    inference(backward_demodulation,[],[f190,f285])).
% 0.19/0.52  fof(f285,plain,(
% 0.19/0.52    ( ! [X0] : (k2_relat_1(k1_wellord2(X0)) = X0) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f284,f213])).
% 0.19/0.52  fof(f213,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(X0,k2_relat_1(k1_wellord2(X0)))) )),
% 0.19/0.52    inference(resolution,[],[f148,f168])).
% 0.19/0.52  fof(f168,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f167,f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,axiom,(
% 0.19/0.52    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.19/0.52  fof(f167,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f166])).
% 0.19/0.52  fof(f166,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.52    inference(resolution,[],[f141,f62])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) & r2_hidden(sK1(X0,X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).
% 0.19/0.52  fof(f141,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f140,f46])).
% 0.19/0.52  fof(f140,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f139,f81])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.52    inference(equality_resolution,[],[f72])).
% 0.19/0.52  fof(f72,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f44])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.52    inference(flattening,[],[f43])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.52    inference(nnf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.52  fof(f139,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1))) | ~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f138])).
% 0.19/0.52  fof(f138,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1))) | ~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | ~r2_hidden(sK1(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 0.19/0.52    inference(resolution,[],[f133,f63])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f37])).
% 0.19/0.52  fof(f133,plain,(
% 0.19/0.52    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f78,f46])).
% 0.19/0.52  fof(f78,plain,(
% 0.19/0.52    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.52    inference(equality_resolution,[],[f66])).
% 0.19/0.52  fof(f66,plain,(
% 0.19/0.52    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f42])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f41])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(rectify,[],[f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(nnf_transformation,[],[f33])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f32])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.19/0.52  fof(f148,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | r1_tarski(X0,k2_relat_1(k1_wellord2(X1)))) )),
% 0.19/0.52    inference(resolution,[],[f125,f46])).
% 0.19/0.52  fof(f125,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k2_relat_1(X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f123,f47])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,axiom,(
% 0.19/0.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.52  fof(f123,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.52    inference(superposition,[],[f55,f50])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,axiom,(
% 0.19/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(flattening,[],[f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.19/0.52  fof(f284,plain,(
% 0.19/0.52    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(k1_wellord2(X0))) | k2_relat_1(k1_wellord2(X0)) = X0) )),
% 0.19/0.52    inference(superposition,[],[f197,f265])).
% 0.19/0.52  fof(f265,plain,(
% 0.19/0.52    ( ! [X0] : (k1_wellord2(X0) = k8_relat_1(X0,k1_wellord2(X0))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f263,f46])).
% 0.19/0.52  fof(f263,plain,(
% 0.19/0.52    ( ! [X0] : (k1_wellord2(X0) = k8_relat_1(X0,k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.52    inference(resolution,[],[f260,f102])).
% 0.19/0.52  fof(f102,plain,(
% 0.19/0.52    ( ! [X6,X7] : (~r1_tarski(X6,k8_relat_1(X7,X6)) | k8_relat_1(X7,X6) = X6 | ~v1_relat_1(X6)) )),
% 0.19/0.52    inference(resolution,[],[f73,f59])).
% 0.19/0.52  fof(f59,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.19/0.52  fof(f73,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f44])).
% 0.19/0.52  fof(f260,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k8_relat_1(X0,k1_wellord2(X0)))) )),
% 0.19/0.52    inference(superposition,[],[f258,f116])).
% 0.19/0.52  fof(f116,plain,(
% 0.19/0.52    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0)) )),
% 0.19/0.52    inference(forward_demodulation,[],[f88,f91])).
% 0.19/0.52  fof(f91,plain,(
% 0.19/0.52    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f80,f46])).
% 0.19/0.52  fof(f80,plain,(
% 0.19/0.52    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.52    inference(equality_resolution,[],[f64])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f42])).
% 0.19/0.52  fof(f88,plain,(
% 0.19/0.52    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0)))) )),
% 0.19/0.52    inference(resolution,[],[f51,f46])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_wellord1(X0,k3_relat_1(X0)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f20])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ! [X0] : (k2_wellord1(X0,k3_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).
% 0.19/0.52  fof(f258,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_wellord1(k1_wellord2(X0),X1),k8_relat_1(X1,k1_wellord2(X0)))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f257,f46])).
% 0.19/0.52  fof(f257,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_wellord1(k1_wellord2(X0),X1),k8_relat_1(X1,k1_wellord2(X0))) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.52    inference(resolution,[],[f160,f57])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.19/0.52  fof(f160,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(k8_relat_1(X0,k1_wellord2(X1))) | r1_tarski(k2_wellord1(k1_wellord2(X1),X0),k8_relat_1(X0,k1_wellord2(X1)))) )),
% 0.19/0.52    inference(superposition,[],[f58,f112])).
% 0.19/0.52  fof(f112,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X0),X1) = k7_relat_1(k8_relat_1(X1,k1_wellord2(X0)),X1)) )),
% 0.19/0.52    inference(resolution,[],[f61,f46])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.19/0.52  fof(f197,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(k8_relat_1(X0,k1_wellord2(X1)))) | k2_relat_1(k8_relat_1(X0,k1_wellord2(X1))) = X0) )),
% 0.19/0.52    inference(resolution,[],[f101,f46])).
% 0.19/0.52  fof(f101,plain,(
% 0.19/0.52    ( ! [X4,X5] : (~v1_relat_1(X5) | k2_relat_1(k8_relat_1(X4,X5)) = X4 | ~r1_tarski(X4,k2_relat_1(k8_relat_1(X4,X5)))) )),
% 0.19/0.52    inference(resolution,[],[f73,f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.19/0.52  fof(f190,plain,(
% 0.19/0.52    ( ! [X6] : (r1_tarski(k1_wellord2(X6),k2_zfmisc_1(X6,k2_relat_1(k1_wellord2(X6))))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f186,f46])).
% 0.19/0.52  fof(f186,plain,(
% 0.19/0.52    ( ! [X6] : (r1_tarski(k1_wellord2(X6),k2_zfmisc_1(X6,k2_relat_1(k1_wellord2(X6)))) | ~v1_relat_1(k1_wellord2(X6))) )),
% 0.19/0.52    inference(superposition,[],[f52,f173])).
% 0.19/0.52  fof(f173,plain,(
% 0.19/0.52    ( ! [X0] : (k1_relat_1(k1_wellord2(X0)) = X0) )),
% 0.19/0.52    inference(resolution,[],[f169,f132])).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(k1_wellord2(X1))) | k1_relat_1(k1_wellord2(X1)) = X1) )),
% 0.19/0.52    inference(superposition,[],[f99,f108])).
% 0.19/0.52  fof(f108,plain,(
% 0.19/0.52    ( ! [X0] : (k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0) )),
% 0.19/0.52    inference(forward_demodulation,[],[f105,f91])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) )),
% 0.19/0.52    inference(resolution,[],[f53,f46])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.19/0.52  fof(f99,plain,(
% 0.19/0.52    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 0.19/0.52    inference(resolution,[],[f73,f56])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.52  fof(f169,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(X0,k1_relat_1(k1_wellord2(X0)))) )),
% 0.19/0.52    inference(resolution,[],[f168,f134])).
% 0.19/0.52  fof(f134,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | r1_tarski(X0,k1_relat_1(k1_wellord2(X1)))) )),
% 0.19/0.52    inference(resolution,[],[f120,f46])).
% 0.19/0.52  fof(f120,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k1_relat_1(X1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f118,f47])).
% 0.19/0.52  fof(f118,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.52    inference(superposition,[],[f54,f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f9])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.19/0.52  fof(f86,plain,(
% 0.19/0.52    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) | spl4_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f84])).
% 0.19/0.52  fof(f84,plain,(
% 0.19/0.52    spl4_1 <=> r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.52  fof(f87,plain,(
% 0.19/0.52    ~spl4_1),
% 0.19/0.52    inference(avatar_split_clause,[],[f45,f84])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,negated_conjecture,(
% 0.19/0.52    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.19/0.52    inference(negated_conjecture,[],[f17])).
% 0.19/0.52  fof(f17,conjecture,(
% 0.19/0.52    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (19258)------------------------------
% 0.19/0.52  % (19258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (19258)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (19258)Memory used [KB]: 6396
% 0.19/0.52  % (19258)Time elapsed: 0.102 s
% 0.19/0.52  % (19258)------------------------------
% 0.19/0.52  % (19258)------------------------------
% 0.19/0.52  % (19257)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (19261)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.52  % (19255)Success in time 0.182 s
%------------------------------------------------------------------------------
