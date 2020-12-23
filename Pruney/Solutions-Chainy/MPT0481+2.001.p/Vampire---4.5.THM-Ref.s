%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:15 EST 2020

% Result     : Theorem 3.36s
% Output     : Refutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 216 expanded)
%              Number of leaves         :    8 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  200 ( 622 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1005,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f327,f973])).

fof(f973,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f972])).

fof(f972,plain,
    ( $false
    | spl10_2 ),
    inference(subsumption_resolution,[],[f958,f342])).

fof(f342,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK1)
    | spl10_2 ),
    inference(resolution,[],[f47,f245])).

fof(f245,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(sK1,k6_relat_1(X0)),X1)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(X0)),X1),sK7(k5_relat_1(sK1,k6_relat_1(X0)),X1)),X1) ) ),
    inference(resolution,[],[f158,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f158,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X2,k6_relat_1(X3)),X4),sK7(k5_relat_1(X2,k6_relat_1(X3)),X4)),X4)
      | r1_tarski(k5_relat_1(X2,k6_relat_1(X3)),X4) ) ),
    inference(resolution,[],[f63,f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f63,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X4)
      | r1_tarski(k5_relat_1(X3,X4),X5)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X3,X4),X5),sK7(k5_relat_1(X3,X4),X5)),X5)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f47,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl10_2
  <=> r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f958,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK1)
    | spl10_2 ),
    inference(backward_demodulation,[],[f926,f942])).

fof(f942,plain,
    ( sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))
    | spl10_2 ),
    inference(resolution,[],[f924,f50])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | X2 = X3 ) ),
    inference(subsumption_resolution,[],[f38,f16])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f924,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),k6_relat_1(sK0))
    | spl10_2 ),
    inference(subsumption_resolution,[],[f923,f15])).

fof(f923,plain,
    ( r2_hidden(k4_tarski(sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f911,f16])).

fof(f911,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | r2_hidden(k4_tarski(sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl10_2 ),
    inference(resolution,[],[f904,f54])).

fof(f54,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f34,f32])).

fof(f34,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1)
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f904,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),k5_relat_1(sK1,k6_relat_1(sK0)))
    | spl10_2 ),
    inference(resolution,[],[f901,f47])).

fof(f901,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(sK1,k6_relat_1(X0)),X1)
      | r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(X0)),X1),sK7(k5_relat_1(sK1,k6_relat_1(X0)),X1)),k5_relat_1(sK1,k6_relat_1(X0))) ) ),
    inference(resolution,[],[f279,f15])).

fof(f279,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(k5_relat_1(X2,k6_relat_1(X3)),X4),sK7(k5_relat_1(X2,k6_relat_1(X3)),X4)),k5_relat_1(X2,k6_relat_1(X3)))
      | r1_tarski(k5_relat_1(X2,k6_relat_1(X3)),X4) ) ),
    inference(resolution,[],[f60,f16])).

fof(f60,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X4)
      | r1_tarski(k5_relat_1(X3,X4),X5)
      | r2_hidden(k4_tarski(sK6(k5_relat_1(X3,X4),X5),sK7(k5_relat_1(X3,X4),X5)),k5_relat_1(X3,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f24,f32])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f926,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))),sK1)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f925,f15])).

fof(f925,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))),sK1)
    | ~ v1_relat_1(sK1)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f912,f16])).

fof(f912,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))),sK1)
    | ~ v1_relat_1(sK1)
    | spl10_2 ),
    inference(resolution,[],[f904,f53])).

fof(f53,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f327,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f316,f163])).

fof(f163,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1)
    | spl10_1 ),
    inference(resolution,[],[f161,f43])).

fof(f43,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl10_1
  <=> r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f161,plain,(
    ! [X2,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X1),sK1),X2)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(X1),sK1),X2),sK7(k5_relat_1(k6_relat_1(X1),sK1),X2)),X2) ) ),
    inference(resolution,[],[f157,f16])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK6(k5_relat_1(X0,sK1),X1),sK7(k5_relat_1(X0,sK1),X1)),X1)
      | r1_tarski(k5_relat_1(X0,sK1),X1) ) ),
    inference(resolution,[],[f63,f15])).

fof(f316,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1)
    | spl10_1 ),
    inference(backward_demodulation,[],[f293,f306])).

fof(f306,plain,
    ( sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1))
    | spl10_1 ),
    inference(resolution,[],[f295,f50])).

fof(f295,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1))),k6_relat_1(sK0))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f294,f16])).

fof(f294,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1))),k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f287,f15])).

fof(f287,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1))),k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl10_1 ),
    inference(resolution,[],[f284,f53])).

fof(f284,plain,
    ( r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),k5_relat_1(k6_relat_1(sK0),sK1))
    | spl10_1 ),
    inference(resolution,[],[f282,f43])).

fof(f282,plain,(
    ! [X2,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X1),sK1),X2)
      | r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(X1),sK1),X2),sK7(k5_relat_1(k6_relat_1(X1),sK1),X2)),k5_relat_1(k6_relat_1(X1),sK1)) ) ),
    inference(resolution,[],[f278,f16])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(k5_relat_1(X0,sK1),X1),sK7(k5_relat_1(X0,sK1),X1)),k5_relat_1(X0,sK1))
      | r1_tarski(k5_relat_1(X0,sK1),X1) ) ),
    inference(resolution,[],[f60,f15])).

fof(f293,plain,
    ( r2_hidden(k4_tarski(sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f292,f16])).

fof(f292,plain,
    ( r2_hidden(k4_tarski(sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f286,f15])).

fof(f286,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl10_1 ),
    inference(resolution,[],[f284,f54])).

fof(f48,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f14,f45,f41])).

fof(f14,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:27:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (31597)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (31589)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (31593)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (31580)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (31601)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (31586)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (31587)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (31583)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (31592)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (31576)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (31585)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (31575)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (31578)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.54  % (31598)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (31590)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (31600)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (31584)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (31579)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (31596)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.55  % (31588)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.55  % (31581)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (31577)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.56  % (31595)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.56  % (31594)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.56  % (31599)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.56  % (31591)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 2.13/0.68  % (31585)Refutation not found, incomplete strategy% (31585)------------------------------
% 2.13/0.68  % (31585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.68  % (31585)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.68  
% 2.13/0.68  % (31585)Memory used [KB]: 6012
% 2.13/0.68  % (31585)Time elapsed: 0.253 s
% 2.13/0.68  % (31585)------------------------------
% 2.13/0.68  % (31585)------------------------------
% 3.36/0.81  % (31598)Refutation found. Thanks to Tanya!
% 3.36/0.81  % SZS status Theorem for theBenchmark
% 3.36/0.81  % SZS output start Proof for theBenchmark
% 3.36/0.81  fof(f1005,plain,(
% 3.36/0.81    $false),
% 3.36/0.81    inference(avatar_sat_refutation,[],[f48,f327,f973])).
% 3.36/0.81  fof(f973,plain,(
% 3.36/0.81    spl10_2),
% 3.36/0.81    inference(avatar_contradiction_clause,[],[f972])).
% 3.36/0.81  fof(f972,plain,(
% 3.36/0.81    $false | spl10_2),
% 3.36/0.81    inference(subsumption_resolution,[],[f958,f342])).
% 3.36/0.81  fof(f342,plain,(
% 3.36/0.81    ~r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK1) | spl10_2),
% 3.36/0.81    inference(resolution,[],[f47,f245])).
% 3.36/0.81  fof(f245,plain,(
% 3.36/0.81    ( ! [X0,X1] : (r1_tarski(k5_relat_1(sK1,k6_relat_1(X0)),X1) | ~r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(X0)),X1),sK7(k5_relat_1(sK1,k6_relat_1(X0)),X1)),X1)) )),
% 3.36/0.81    inference(resolution,[],[f158,f15])).
% 3.36/0.81  fof(f15,plain,(
% 3.36/0.81    v1_relat_1(sK1)),
% 3.36/0.81    inference(cnf_transformation,[],[f8])).
% 3.36/0.81  fof(f8,plain,(
% 3.36/0.81    ? [X0,X1] : ((~r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) & v1_relat_1(X1))),
% 3.36/0.81    inference(ennf_transformation,[],[f7])).
% 3.36/0.81  fof(f7,negated_conjecture,(
% 3.36/0.81    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.36/0.81    inference(negated_conjecture,[],[f6])).
% 3.36/0.81  fof(f6,conjecture,(
% 3.36/0.81    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.36/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 3.36/0.81  fof(f158,plain,(
% 3.36/0.81    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(sK6(k5_relat_1(X2,k6_relat_1(X3)),X4),sK7(k5_relat_1(X2,k6_relat_1(X3)),X4)),X4) | r1_tarski(k5_relat_1(X2,k6_relat_1(X3)),X4)) )),
% 3.36/0.81    inference(resolution,[],[f63,f16])).
% 3.36/0.81  fof(f16,plain,(
% 3.36/0.81    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.36/0.81    inference(cnf_transformation,[],[f5])).
% 3.36/0.81  fof(f5,axiom,(
% 3.36/0.81    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.36/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 3.36/0.81  fof(f63,plain,(
% 3.36/0.81    ( ! [X4,X5,X3] : (~v1_relat_1(X4) | r1_tarski(k5_relat_1(X3,X4),X5) | ~r2_hidden(k4_tarski(sK6(k5_relat_1(X3,X4),X5),sK7(k5_relat_1(X3,X4),X5)),X5) | ~v1_relat_1(X3)) )),
% 3.36/0.81    inference(resolution,[],[f25,f32])).
% 3.36/0.81  fof(f32,plain,(
% 3.36/0.81    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/0.81    inference(cnf_transformation,[],[f13])).
% 3.36/0.81  fof(f13,plain,(
% 3.36/0.81    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.36/0.81    inference(flattening,[],[f12])).
% 3.36/0.81  fof(f12,plain,(
% 3.36/0.81    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.36/0.81    inference(ennf_transformation,[],[f4])).
% 3.36/0.81  fof(f4,axiom,(
% 3.36/0.81    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.36/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 3.36/0.81  fof(f25,plain,(
% 3.36/0.81    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 3.36/0.81    inference(cnf_transformation,[],[f10])).
% 3.36/0.81  fof(f10,plain,(
% 3.36/0.81    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 3.36/0.81    inference(ennf_transformation,[],[f2])).
% 3.36/0.81  fof(f2,axiom,(
% 3.36/0.81    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 3.36/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 3.36/0.82  fof(f47,plain,(
% 3.36/0.82    ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) | spl10_2),
% 3.36/0.82    inference(avatar_component_clause,[],[f45])).
% 3.36/0.82  fof(f45,plain,(
% 3.36/0.82    spl10_2 <=> r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),
% 3.36/0.82    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 3.36/0.82  fof(f958,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK1) | spl10_2),
% 3.36/0.82    inference(backward_demodulation,[],[f926,f942])).
% 3.36/0.82  fof(f942,plain,(
% 3.36/0.82    sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) = sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)) | spl10_2),
% 3.36/0.82    inference(resolution,[],[f924,f50])).
% 3.36/0.82  fof(f50,plain,(
% 3.36/0.82    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) | X2 = X3) )),
% 3.36/0.82    inference(subsumption_resolution,[],[f38,f16])).
% 3.36/0.82  fof(f38,plain,(
% 3.36/0.82    ( ! [X2,X0,X3] : (~v1_relat_1(k6_relat_1(X0)) | X2 = X3 | ~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))) )),
% 3.36/0.82    inference(equality_resolution,[],[f30])).
% 3.36/0.82  fof(f30,plain,(
% 3.36/0.82    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | X2 = X3 | ~r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 3.36/0.82    inference(cnf_transformation,[],[f11])).
% 3.36/0.82  fof(f11,plain,(
% 3.36/0.82    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 3.36/0.82    inference(ennf_transformation,[],[f1])).
% 3.36/0.82  fof(f1,axiom,(
% 3.36/0.82    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 3.36/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).
% 3.36/0.82  fof(f924,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),k6_relat_1(sK0)) | spl10_2),
% 3.36/0.82    inference(subsumption_resolution,[],[f923,f15])).
% 3.36/0.82  fof(f923,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),k6_relat_1(sK0)) | ~v1_relat_1(sK1) | spl10_2),
% 3.36/0.82    inference(subsumption_resolution,[],[f911,f16])).
% 3.36/0.82  fof(f911,plain,(
% 3.36/0.82    ~v1_relat_1(k6_relat_1(sK0)) | r2_hidden(k4_tarski(sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),k6_relat_1(sK0)) | ~v1_relat_1(sK1) | spl10_2),
% 3.36/0.82    inference(resolution,[],[f904,f54])).
% 3.36/0.82  fof(f54,plain,(
% 3.36/0.82    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1) | ~v1_relat_1(X0)) )),
% 3.36/0.82    inference(subsumption_resolution,[],[f34,f32])).
% 3.36/0.82  fof(f34,plain,(
% 3.36/0.82    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 3.36/0.82    inference(equality_resolution,[],[f21])).
% 3.36/0.82  fof(f21,plain,(
% 3.36/0.82    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK4(X0,X1,X3,X4),X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 3.36/0.82    inference(cnf_transformation,[],[f9])).
% 3.36/0.82  fof(f9,plain,(
% 3.36/0.82    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/0.82    inference(ennf_transformation,[],[f3])).
% 3.36/0.82  fof(f3,axiom,(
% 3.36/0.82    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 3.36/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 3.36/0.82  fof(f904,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)),k5_relat_1(sK1,k6_relat_1(sK0))) | spl10_2),
% 3.36/0.82    inference(resolution,[],[f901,f47])).
% 3.36/0.82  fof(f901,plain,(
% 3.36/0.82    ( ! [X0,X1] : (r1_tarski(k5_relat_1(sK1,k6_relat_1(X0)),X1) | r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(X0)),X1),sK7(k5_relat_1(sK1,k6_relat_1(X0)),X1)),k5_relat_1(sK1,k6_relat_1(X0)))) )),
% 3.36/0.82    inference(resolution,[],[f279,f15])).
% 3.36/0.82  fof(f279,plain,(
% 3.36/0.82    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(k5_relat_1(X2,k6_relat_1(X3)),X4),sK7(k5_relat_1(X2,k6_relat_1(X3)),X4)),k5_relat_1(X2,k6_relat_1(X3))) | r1_tarski(k5_relat_1(X2,k6_relat_1(X3)),X4)) )),
% 3.36/0.82    inference(resolution,[],[f60,f16])).
% 3.36/0.82  fof(f60,plain,(
% 3.36/0.82    ( ! [X4,X5,X3] : (~v1_relat_1(X4) | r1_tarski(k5_relat_1(X3,X4),X5) | r2_hidden(k4_tarski(sK6(k5_relat_1(X3,X4),X5),sK7(k5_relat_1(X3,X4),X5)),k5_relat_1(X3,X4)) | ~v1_relat_1(X3)) )),
% 3.36/0.82    inference(resolution,[],[f24,f32])).
% 3.36/0.82  fof(f24,plain,(
% 3.36/0.82    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 3.36/0.82    inference(cnf_transformation,[],[f10])).
% 3.36/0.82  fof(f926,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))),sK1) | spl10_2),
% 3.36/0.82    inference(subsumption_resolution,[],[f925,f15])).
% 3.36/0.82  fof(f925,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))),sK1) | ~v1_relat_1(sK1) | spl10_2),
% 3.36/0.82    inference(subsumption_resolution,[],[f912,f16])).
% 3.36/0.82  fof(f912,plain,(
% 3.36/0.82    ~v1_relat_1(k6_relat_1(sK0)) | r2_hidden(k4_tarski(sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK4(sK1,k6_relat_1(sK0),sK6(k5_relat_1(sK1,k6_relat_1(sK0)),sK1),sK7(k5_relat_1(sK1,k6_relat_1(sK0)),sK1))),sK1) | ~v1_relat_1(sK1) | spl10_2),
% 3.36/0.82    inference(resolution,[],[f904,f53])).
% 3.36/0.82  fof(f53,plain,(
% 3.36/0.82    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0) | ~v1_relat_1(X0)) )),
% 3.36/0.82    inference(subsumption_resolution,[],[f35,f32])).
% 3.36/0.82  fof(f35,plain,(
% 3.36/0.82    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))) )),
% 3.36/0.82    inference(equality_resolution,[],[f20])).
% 3.36/0.82  fof(f20,plain,(
% 3.36/0.82    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,sK4(X0,X1,X3,X4)),X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k5_relat_1(X0,X1) != X2) )),
% 3.36/0.82    inference(cnf_transformation,[],[f9])).
% 3.36/0.82  fof(f327,plain,(
% 3.36/0.82    spl10_1),
% 3.36/0.82    inference(avatar_contradiction_clause,[],[f326])).
% 3.36/0.82  fof(f326,plain,(
% 3.36/0.82    $false | spl10_1),
% 3.36/0.82    inference(subsumption_resolution,[],[f316,f163])).
% 3.36/0.82  fof(f163,plain,(
% 3.36/0.82    ~r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1) | spl10_1),
% 3.36/0.82    inference(resolution,[],[f161,f43])).
% 3.36/0.82  fof(f43,plain,(
% 3.36/0.82    ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) | spl10_1),
% 3.36/0.82    inference(avatar_component_clause,[],[f41])).
% 3.36/0.82  fof(f41,plain,(
% 3.36/0.82    spl10_1 <=> r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 3.36/0.82    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 3.36/0.82  fof(f161,plain,(
% 3.36/0.82    ( ! [X2,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X1),sK1),X2) | ~r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(X1),sK1),X2),sK7(k5_relat_1(k6_relat_1(X1),sK1),X2)),X2)) )),
% 3.36/0.82    inference(resolution,[],[f157,f16])).
% 3.36/0.82  fof(f157,plain,(
% 3.36/0.82    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK6(k5_relat_1(X0,sK1),X1),sK7(k5_relat_1(X0,sK1),X1)),X1) | r1_tarski(k5_relat_1(X0,sK1),X1)) )),
% 3.36/0.82    inference(resolution,[],[f63,f15])).
% 3.36/0.82  fof(f316,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1) | spl10_1),
% 3.36/0.82    inference(backward_demodulation,[],[f293,f306])).
% 3.36/0.82  fof(f306,plain,(
% 3.36/0.82    sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1) = sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)) | spl10_1),
% 3.36/0.82    inference(resolution,[],[f295,f50])).
% 3.36/0.82  fof(f295,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1))),k6_relat_1(sK0)) | spl10_1),
% 3.36/0.82    inference(subsumption_resolution,[],[f294,f16])).
% 3.36/0.82  fof(f294,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1))),k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | spl10_1),
% 3.36/0.82    inference(subsumption_resolution,[],[f287,f15])).
% 3.36/0.82  fof(f287,plain,(
% 3.36/0.82    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1))),k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | spl10_1),
% 3.36/0.82    inference(resolution,[],[f284,f53])).
% 3.36/0.82  fof(f284,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),k5_relat_1(k6_relat_1(sK0),sK1)) | spl10_1),
% 3.36/0.82    inference(resolution,[],[f282,f43])).
% 3.36/0.82  fof(f282,plain,(
% 3.36/0.82    ( ! [X2,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X1),sK1),X2) | r2_hidden(k4_tarski(sK6(k5_relat_1(k6_relat_1(X1),sK1),X2),sK7(k5_relat_1(k6_relat_1(X1),sK1),X2)),k5_relat_1(k6_relat_1(X1),sK1))) )),
% 3.36/0.82    inference(resolution,[],[f278,f16])).
% 3.36/0.82  fof(f278,plain,(
% 3.36/0.82    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK6(k5_relat_1(X0,sK1),X1),sK7(k5_relat_1(X0,sK1),X1)),k5_relat_1(X0,sK1)) | r1_tarski(k5_relat_1(X0,sK1),X1)) )),
% 3.36/0.82    inference(resolution,[],[f60,f15])).
% 3.36/0.82  fof(f293,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1) | spl10_1),
% 3.36/0.82    inference(subsumption_resolution,[],[f292,f16])).
% 3.36/0.82  fof(f292,plain,(
% 3.36/0.82    r2_hidden(k4_tarski(sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | spl10_1),
% 3.36/0.82    inference(subsumption_resolution,[],[f286,f15])).
% 3.36/0.82  fof(f286,plain,(
% 3.36/0.82    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK4(k6_relat_1(sK0),sK1,sK6(k5_relat_1(k6_relat_1(sK0),sK1),sK1),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK7(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | spl10_1),
% 3.36/0.82    inference(resolution,[],[f284,f54])).
% 3.36/0.82  fof(f48,plain,(
% 3.36/0.82    ~spl10_1 | ~spl10_2),
% 3.36/0.82    inference(avatar_split_clause,[],[f14,f45,f41])).
% 3.36/0.82  fof(f14,plain,(
% 3.36/0.82    ~r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) | ~r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)),
% 3.36/0.82    inference(cnf_transformation,[],[f8])).
% 3.36/0.82  % SZS output end Proof for theBenchmark
% 3.36/0.82  % (31598)------------------------------
% 3.36/0.82  % (31598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.82  % (31598)Termination reason: Refutation
% 3.36/0.82  
% 3.36/0.82  % (31598)Memory used [KB]: 13304
% 3.36/0.82  % (31598)Time elapsed: 0.359 s
% 3.36/0.82  % (31598)------------------------------
% 3.36/0.82  % (31598)------------------------------
% 3.36/0.84  % (31573)Success in time 0.477 s
%------------------------------------------------------------------------------
