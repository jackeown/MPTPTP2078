%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0481+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:04 EST 2020

% Result     : Theorem 3.03s
% Output     : Refutation 3.03s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

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
