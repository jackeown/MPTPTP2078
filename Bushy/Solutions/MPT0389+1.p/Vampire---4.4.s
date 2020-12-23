%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t7_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 8.84s
% Output     : Refutation 8.84s
% Verified   : 
% Statistics : Number of formulae       :   49 (  82 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   16
%              Number of atoms          :  130 ( 250 expanded)
%              Number of equality atoms :   46 (  93 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15888,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15887,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f78,f68])).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f67,f37])).

fof(f37,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',dt_o_0_0_xboole_0)).

fof(f67,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f38,f37])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t6_boole)).

fof(f78,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X2)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t7_boole)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',d3_tarski)).

fof(f15887,plain,(
    ~ r1_tarski(k1_xboole_0,k1_setfam_1(sK0)) ),
    inference(forward_demodulation,[],[f15600,f61])).

fof(f61,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',d1_setfam_1)).

fof(f15600,plain,(
    ~ r1_tarski(k1_setfam_1(k1_xboole_0),k1_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f15598,f36])).

fof(f36,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t7_setfam_1.p',t7_setfam_1)).

fof(f15598,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f15597,f36])).

fof(f15597,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f15586])).

fof(f15586,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | k1_xboole_0 = sK1
    | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(resolution,[],[f15579,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15579,plain,(
    ! [X1] :
      ( r2_hidden(sK6(k1_setfam_1(sK1),X1),k1_setfam_1(sK0))
      | r1_tarski(k1_setfam_1(sK1),X1)
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f15577,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f15577,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK1
      | r1_tarski(k1_setfam_1(sK1),X1)
      | r2_hidden(sK6(k1_setfam_1(sK1),X1),k1_setfam_1(sK0))
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f15567])).

fof(f15567,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK1
      | r1_tarski(k1_setfam_1(sK1),X1)
      | r2_hidden(sK6(k1_setfam_1(sK1),X1),k1_setfam_1(sK0))
      | k1_xboole_0 = sK0
      | r2_hidden(sK6(k1_setfam_1(sK1),X1),k1_setfam_1(sK0)) ) ),
    inference(resolution,[],[f1116,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,sK4(X0,X2))
      | k1_xboole_0 = X0
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,sK4(X0,X2))
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1116,plain,(
    ! [X26,X25] :
      ( r2_hidden(sK6(k1_setfam_1(sK1),X25),sK4(sK0,X26))
      | k1_xboole_0 = sK1
      | r1_tarski(k1_setfam_1(sK1),X25)
      | r2_hidden(X26,k1_setfam_1(sK0)) ) ),
    inference(resolution,[],[f302,f755])).

fof(f755,plain,(
    ! [X8] :
      ( r2_hidden(sK4(sK0,X8),sK1)
      | r2_hidden(X8,k1_setfam_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f750,f35])).

fof(f750,plain,(
    ! [X8] :
      ( r2_hidden(X8,k1_setfam_1(sK0))
      | r2_hidden(sK4(sK0,X8),sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f204,f34])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f204,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X5,X7)
      | r2_hidden(X6,k1_setfam_1(X5))
      | r2_hidden(sK4(X5,X6),X7)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),X0)
      | k1_xboole_0 = X0
      | r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0,X2),X0)
      | r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK6(k1_setfam_1(X1),X2),X0)
      | k1_xboole_0 = X1
      | r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(resolution,[],[f66,f52])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,k1_setfam_1(X0))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
