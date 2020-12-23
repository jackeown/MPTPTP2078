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
% DateTime   : Thu Dec  3 13:00:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 187 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   24
%              Number of atoms          :  294 ( 704 expanded)
%              Number of equality atoms :   56 ( 126 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f501,plain,(
    $false ),
    inference(resolution,[],[f381,f43])).

fof(f43,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f32])).

fof(f32,plain,
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

fof(f381,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(forward_demodulation,[],[f372,f357])).

fof(f357,plain,(
    ! [X0] : k1_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f340,f184])).

fof(f184,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k1_wellord2(X1)))
      | k1_relat_1(k1_wellord2(X1)) = X1 ) ),
    inference(superposition,[],[f91,f96])).

fof(f96,plain,(
    ! [X1] : k2_xboole_0(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))) = X1 ),
    inference(forward_demodulation,[],[f93,f81])).

fof(f81,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f76,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f76,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f39])).

fof(f39,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f93,plain,(
    ! [X1] : k3_relat_1(k1_wellord2(X1)) = k2_xboole_0(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))) ),
    inference(resolution,[],[f49,f45])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f340,plain,(
    ! [X3] : r1_tarski(X3,k1_relat_1(k1_wellord2(X3))) ),
    inference(forward_demodulation,[],[f339,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f339,plain,(
    ! [X3] : r1_tarski(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k1_wellord2(X3))) ),
    inference(subsumption_resolution,[],[f338,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f338,plain,(
    ! [X3] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k1_wellord2(X3)))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f332,f45])).

fof(f332,plain,(
    ! [X3] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k1_wellord2(X3)))
      | ~ v1_relat_1(k1_wellord2(X3))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(resolution,[],[f327,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
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

fof(f327,plain,(
    ! [X2] : r1_tarski(k6_relat_1(X2),k1_wellord2(X2)) ),
    inference(subsumption_resolution,[],[f325,f45])).

fof(f325,plain,(
    ! [X2] :
      ( r1_tarski(k6_relat_1(X2),k1_wellord2(X2))
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,(
    ! [X2] :
      ( r1_tarski(k6_relat_1(X2),k1_wellord2(X2))
      | r1_tarski(k6_relat_1(X2),k1_wellord2(X2))
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(resolution,[],[f193,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1)
        & r2_hidden(sK1(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f193,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1))),k1_wellord2(X0))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) ) ),
    inference(resolution,[],[f110,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1)) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f79,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X4,X0,X5] :
      ( ~ r1_tarski(X4,X5)
      | r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f74,f45])).

fof(f74,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f110,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK1(X2,k1_wellord2(X3)),X2)
      | r1_tarski(k6_relat_1(X2),k1_wellord2(X3)) ) ),
    inference(resolution,[],[f57,f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f372,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X0)) ),
    inference(superposition,[],[f87,f348])).

fof(f348,plain,(
    ! [X5] : k2_relat_1(k1_wellord2(X5)) = X5 ),
    inference(subsumption_resolution,[],[f347,f252])).

fof(f252,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) ),
    inference(superposition,[],[f244,f101])).

fof(f101,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0) ),
    inference(resolution,[],[f66,f77])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f244,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_wellord1(k1_wellord2(X1),X0)),X0) ),
    inference(superposition,[],[f118,f104])).

fof(f104,plain,(
    ! [X2,X3] : k2_wellord1(k1_wellord2(X2),X3) = k8_relat_1(X3,k7_relat_1(k1_wellord2(X2),X3)) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f118,plain,(
    ! [X8,X7,X9] : r1_tarski(k2_relat_1(k8_relat_1(X7,k7_relat_1(k1_wellord2(X8),X9))),X7) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(f83,plain,(
    ! [X2,X3] : v1_relat_1(k7_relat_1(k1_wellord2(X2),X3)) ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f347,plain,(
    ! [X5] :
      ( k2_relat_1(k1_wellord2(X5)) = X5
      | ~ r1_tarski(k2_relat_1(k1_wellord2(X5)),X5) ) ),
    inference(resolution,[],[f337,f69])).

fof(f337,plain,(
    ! [X2] : r1_tarski(X2,k2_relat_1(k1_wellord2(X2))) ),
    inference(forward_demodulation,[],[f336,f47])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f336,plain,(
    ! [X2] : r1_tarski(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k1_wellord2(X2))) ),
    inference(subsumption_resolution,[],[f335,f44])).

fof(f335,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k1_wellord2(X2)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f331,f45])).

fof(f331,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k1_wellord2(X2)))
      | ~ v1_relat_1(k1_wellord2(X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f327,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1)))) ),
    inference(resolution,[],[f48,f45])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (17408)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.47  % (17416)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (17408)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f501,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(resolution,[],[f381,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f372,f357])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.49    inference(resolution,[],[f340,f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(k1_wellord2(X1))) | k1_relat_1(k1_wellord2(X1)) = X1) )),
% 0.21/0.49    inference(superposition,[],[f91,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X1] : (k2_xboole_0(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))) = X1) )),
% 0.21/0.49    inference(forward_demodulation,[],[f93,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f76,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(rectify,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X1] : (k3_relat_1(k1_wellord2(X1)) = k2_xboole_0(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1)))) )),
% 0.21/0.49    inference(resolution,[],[f49,f45])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 0.21/0.49    inference(resolution,[],[f69,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    ( ! [X3] : (r1_tarski(X3,k1_relat_1(k1_wellord2(X3)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f339,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    ( ! [X3] : (r1_tarski(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k1_wellord2(X3)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f338,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    ( ! [X3] : (r1_tarski(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k1_wellord2(X3))) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f332,f45])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    ( ! [X3] : (r1_tarski(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k1_wellord2(X3))) | ~v1_relat_1(k1_wellord2(X3)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.21/0.49    inference(resolution,[],[f327,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    ( ! [X2] : (r1_tarski(k6_relat_1(X2),k1_wellord2(X2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f325,f45])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    ( ! [X2] : (r1_tarski(k6_relat_1(X2),k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(X2))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f323])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    ( ! [X2] : (r1_tarski(k6_relat_1(X2),k1_wellord2(X2)) | r1_tarski(k6_relat_1(X2),k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(X2))) )),
% 0.21/0.49    inference(resolution,[],[f193,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) & r2_hidden(sK1(X0,X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,k1_wellord2(X1)),sK1(X0,k1_wellord2(X1))),k1_wellord2(X0)) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))) )),
% 0.21/0.49    inference(resolution,[],[f110,f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X0),k1_wellord2(X1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f79,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X4,X0,X5] : (~r1_tarski(X4,X5) | r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f45])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(sK1(X2,k1_wellord2(X3)),X2) | r1_tarski(k6_relat_1(X2),k1_wellord2(X3))) )),
% 0.21/0.49    inference(resolution,[],[f57,f45])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK1(X0,X1),X0) | r1_tarski(k6_relat_1(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X0))) )),
% 0.21/0.49    inference(superposition,[],[f87,f348])).
% 0.21/0.49  fof(f348,plain,(
% 0.21/0.49    ( ! [X5] : (k2_relat_1(k1_wellord2(X5)) = X5) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f347,f252])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k2_relat_1(k1_wellord2(X0)),X0)) )),
% 0.21/0.49    inference(superposition,[],[f244,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0)) )),
% 0.21/0.49    inference(resolution,[],[f66,f77])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_wellord1(k1_wellord2(X1),X0)),X0)) )),
% 0.21/0.49    inference(superposition,[],[f118,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k2_wellord1(k1_wellord2(X2),X3) = k8_relat_1(X3,k7_relat_1(k1_wellord2(X2),X3))) )),
% 0.21/0.49    inference(resolution,[],[f55,f45])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X8,X7,X9] : (r1_tarski(k2_relat_1(k8_relat_1(X7,k7_relat_1(k1_wellord2(X8),X9))),X7)) )),
% 0.21/0.49    inference(resolution,[],[f83,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X3] : (v1_relat_1(k7_relat_1(k1_wellord2(X2),X3))) )),
% 0.21/0.49    inference(resolution,[],[f53,f45])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    ( ! [X5] : (k2_relat_1(k1_wellord2(X5)) = X5 | ~r1_tarski(k2_relat_1(k1_wellord2(X5)),X5)) )),
% 0.21/0.49    inference(resolution,[],[f337,f69])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    ( ! [X2] : (r1_tarski(X2,k2_relat_1(k1_wellord2(X2)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f336,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    ( ! [X2] : (r1_tarski(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k1_wellord2(X2)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f335,f44])).
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    ( ! [X2] : (r1_tarski(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k1_wellord2(X2))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f331,f45])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    ( ! [X2] : (r1_tarski(k2_relat_1(k6_relat_1(X2)),k2_relat_1(k1_wellord2(X2))) | ~v1_relat_1(k1_wellord2(X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.21/0.49    inference(resolution,[],[f327,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))))) )),
% 0.21/0.49    inference(resolution,[],[f48,f45])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17408)------------------------------
% 0.21/0.49  % (17408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17408)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17408)Memory used [KB]: 11129
% 0.21/0.49  % (17408)Time elapsed: 0.071 s
% 0.21/0.49  % (17408)------------------------------
% 0.21/0.49  % (17408)------------------------------
% 0.21/0.49  % (17397)Success in time 0.138 s
%------------------------------------------------------------------------------
