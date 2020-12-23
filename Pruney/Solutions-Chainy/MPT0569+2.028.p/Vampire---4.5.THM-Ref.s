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
% DateTime   : Thu Dec  3 12:50:30 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   81 (3408 expanded)
%              Number of leaves         :   13 ( 923 expanded)
%              Depth                    :   28
%              Number of atoms          :  262 (15485 expanded)
%              Number of equality atoms :   44 (1707 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f834,plain,(
    $false ),
    inference(subsumption_resolution,[],[f833,f575])).

fof(f575,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f131,f559])).

fof(f559,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f34,f558])).

fof(f558,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k10_relat_1(sK1,k1_xboole_0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f557])).

fof(f557,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k10_relat_1(sK1,k1_xboole_0) = X0
      | k10_relat_1(sK1,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f336,f168])).

fof(f168,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k10_relat_1(sK1,k1_xboole_0),X0),X0)
      | k10_relat_1(sK1,k1_xboole_0) = X0 ) ),
    inference(forward_demodulation,[],[f159,f152])).

fof(f152,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f131,f131,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f159,plain,(
    ! [X0] :
      ( k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = X0
      | r2_hidden(sK3(k10_relat_1(sK1,k1_xboole_0),X0),X0) ) ),
    inference(resolution,[],[f131,f41])).

fof(f336,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(k10_relat_1(sK1,k1_xboole_0),X2),X3)
      | ~ r1_xboole_0(X3,X2)
      | k10_relat_1(sK1,k1_xboole_0) = X2 ) ),
    inference(resolution,[],[f168,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f123,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f123,plain,(
    ! [X0] : r1_xboole_0(X0,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f34,f121])).

fof(f121,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X4)
      | r1_xboole_0(X5,k10_relat_1(sK1,X4)) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X4)
      | r1_xboole_0(X5,k10_relat_1(sK1,X4))
      | r1_xboole_0(X5,k10_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f65,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK2(X0,k10_relat_1(sK1,X1)),X1,sK1),X1)
      | r1_xboole_0(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k10_relat_1(sK1,X3))
      | r2_hidden(sK6(X2,X3,sK1),X3) ) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK6(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
            & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
        & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(sK2(X0,k10_relat_1(sK1,X1)),X1,sK1),X2)
      | ~ r1_xboole_0(X2,X1)
      | r1_xboole_0(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f56,f37])).

fof(f833,plain,(
    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f827,f592])).

fof(f592,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f585])).

% (23940)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f585,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f341,f559])).

fof(f341,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f168,f91])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0) ) ),
    inference(resolution,[],[f88,f43])).

fof(f88,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f86,f36])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0,k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0)
      | r1_xboole_0(X0,k10_relat_1(sK1,sK0)) ) ),
    inference(resolution,[],[f71,f56])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,sK1),sK0)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | k1_xboole_0 = k10_relat_1(sK1,sK0) ) ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,
    ( r1_xboole_0(sK0,k2_relat_1(sK1))
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f32,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X4,k2_relat_1(sK1))
      | ~ r2_hidden(X2,k10_relat_1(sK1,X3))
      | ~ r2_hidden(sK6(X2,X3,sK1),X4) ) ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK6(X3,X4,sK1),k2_relat_1(sK1))
      | ~ r2_hidden(X3,k10_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f50,f48])).

fof(f48,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(X0,X1,sK1)),sK1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f827,plain,(
    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f606,f605,f721,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f721,plain,(
    r2_hidden(k4_tarski(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f605,f49])).

fof(f49,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f605,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f603,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f603,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f602])).

fof(f602,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f33,f592])).

fof(f33,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f606,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f603,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (23936)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (23944)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (23934)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (23942)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (23932)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (23930)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (23931)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (23930)Refutation not found, incomplete strategy% (23930)------------------------------
% 0.21/0.50  % (23930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23930)Memory used [KB]: 6140
% 0.21/0.50  % (23930)Time elapsed: 0.072 s
% 0.21/0.50  % (23930)------------------------------
% 0.21/0.50  % (23930)------------------------------
% 0.21/0.50  % (23945)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (23937)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (23943)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (23947)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (23948)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (23931)Refutation not found, incomplete strategy% (23931)------------------------------
% 0.21/0.51  % (23931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23939)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (23931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23931)Memory used [KB]: 10618
% 0.21/0.52  % (23931)Time elapsed: 0.093 s
% 0.21/0.52  % (23931)------------------------------
% 0.21/0.52  % (23931)------------------------------
% 0.21/0.52  % (23950)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (23935)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (23941)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (23933)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (23938)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.29/0.53  % (23945)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % SZS output start Proof for theBenchmark
% 1.29/0.53  fof(f834,plain,(
% 1.29/0.53    $false),
% 1.29/0.53    inference(subsumption_resolution,[],[f833,f575])).
% 1.29/0.53  fof(f575,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.29/0.53    inference(backward_demodulation,[],[f131,f559])).
% 1.29/0.53  fof(f559,plain,(
% 1.29/0.53    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f34,f558])).
% 1.29/0.53  fof(f558,plain,(
% 1.29/0.53    ( ! [X0] : (~r1_xboole_0(X0,X0) | k10_relat_1(sK1,k1_xboole_0) = X0) )),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f557])).
% 1.29/0.53  fof(f557,plain,(
% 1.29/0.53    ( ! [X0] : (~r1_xboole_0(X0,X0) | k10_relat_1(sK1,k1_xboole_0) = X0 | k10_relat_1(sK1,k1_xboole_0) = X0) )),
% 1.29/0.53    inference(resolution,[],[f336,f168])).
% 1.29/0.53  fof(f168,plain,(
% 1.29/0.53    ( ! [X0] : (r2_hidden(sK3(k10_relat_1(sK1,k1_xboole_0),X0),X0) | k10_relat_1(sK1,k1_xboole_0) = X0) )),
% 1.29/0.53    inference(forward_demodulation,[],[f159,f152])).
% 1.29/0.53  fof(f152,plain,(
% 1.29/0.53    k10_relat_1(sK1,k1_xboole_0) = k2_relat_1(k10_relat_1(sK1,k1_xboole_0))),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f131,f131,f41])).
% 1.29/0.53  fof(f41,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f26])).
% 1.29/0.53  fof(f26,plain,(
% 1.29/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 1.29/0.53  fof(f23,plain,(
% 1.29/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f24,plain,(
% 1.29/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.29/0.53    inference(rectify,[],[f21])).
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.29/0.53    inference(nnf_transformation,[],[f5])).
% 1.29/0.53  fof(f5,axiom,(
% 1.29/0.53    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.29/0.53  fof(f159,plain,(
% 1.29/0.53    ( ! [X0] : (k2_relat_1(k10_relat_1(sK1,k1_xboole_0)) = X0 | r2_hidden(sK3(k10_relat_1(sK1,k1_xboole_0),X0),X0)) )),
% 1.29/0.53    inference(resolution,[],[f131,f41])).
% 1.29/0.53  fof(f336,plain,(
% 1.29/0.53    ( ! [X2,X3] : (~r2_hidden(sK3(k10_relat_1(sK1,k1_xboole_0),X2),X3) | ~r1_xboole_0(X3,X2) | k10_relat_1(sK1,k1_xboole_0) = X2) )),
% 1.29/0.53    inference(resolution,[],[f168,f37])).
% 1.29/0.53  fof(f37,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f20])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f11,plain,(
% 1.29/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.29/0.53    inference(ennf_transformation,[],[f9])).
% 1.29/0.53  fof(f9,plain,(
% 1.29/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.29/0.53    inference(rectify,[],[f2])).
% 1.29/0.53  fof(f2,axiom,(
% 1.29/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.29/0.53  fof(f34,plain,(
% 1.29/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f3])).
% 1.29/0.53  fof(f3,axiom,(
% 1.29/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.29/0.53  fof(f131,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f123,f43])).
% 1.29/0.53  fof(f43,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f13])).
% 1.29/0.53  fof(f13,plain,(
% 1.29/0.53    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f4])).
% 1.29/0.53  fof(f4,axiom,(
% 1.29/0.53    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.29/0.53  fof(f123,plain,(
% 1.29/0.53    ( ! [X0] : (r1_xboole_0(X0,k10_relat_1(sK1,k1_xboole_0))) )),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f34,f121])).
% 1.29/0.53  fof(f121,plain,(
% 1.29/0.53    ( ! [X4,X5] : (~r1_xboole_0(X4,X4) | r1_xboole_0(X5,k10_relat_1(sK1,X4))) )),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f118])).
% 1.29/0.53  fof(f118,plain,(
% 1.29/0.53    ( ! [X4,X5] : (~r1_xboole_0(X4,X4) | r1_xboole_0(X5,k10_relat_1(sK1,X4)) | r1_xboole_0(X5,k10_relat_1(sK1,X4))) )),
% 1.29/0.53    inference(resolution,[],[f65,f56])).
% 1.29/0.53  fof(f56,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r2_hidden(sK6(sK2(X0,k10_relat_1(sK1,X1)),X1,sK1),X1) | r1_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.29/0.53    inference(resolution,[],[f51,f36])).
% 1.29/0.53  fof(f36,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f20])).
% 1.29/0.53  fof(f51,plain,(
% 1.29/0.53    ( ! [X2,X3] : (~r2_hidden(X2,k10_relat_1(sK1,X3)) | r2_hidden(sK6(X2,X3,sK1),X3)) )),
% 1.29/0.53    inference(resolution,[],[f31,f46])).
% 1.29/0.53  fof(f46,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK6(X0,X1,X2),X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f30])).
% 1.29/0.53  fof(f30,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 1.29/0.53  fof(f29,plain,(
% 1.29/0.53    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f28,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.29/0.53    inference(rectify,[],[f27])).
% 1.29/0.53  fof(f27,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.29/0.53    inference(nnf_transformation,[],[f14])).
% 1.29/0.53  fof(f14,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.29/0.53    inference(ennf_transformation,[],[f6])).
% 1.29/0.53  fof(f6,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    v1_relat_1(sK1)),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f16,plain,(
% 1.29/0.53    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.29/0.53    inference(flattening,[],[f15])).
% 1.29/0.53  fof(f15,plain,(
% 1.29/0.53    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.29/0.53    inference(nnf_transformation,[],[f10])).
% 1.29/0.53  fof(f10,plain,(
% 1.29/0.53    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f8])).
% 1.29/0.53  fof(f8,negated_conjecture,(
% 1.29/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.29/0.53    inference(negated_conjecture,[],[f7])).
% 1.29/0.53  fof(f7,conjecture,(
% 1.29/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.29/0.53  fof(f65,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK6(sK2(X0,k10_relat_1(sK1,X1)),X1,sK1),X2) | ~r1_xboole_0(X2,X1) | r1_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.29/0.53    inference(resolution,[],[f56,f37])).
% 1.29/0.53  fof(f833,plain,(
% 1.29/0.53    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)),
% 1.29/0.53    inference(forward_demodulation,[],[f827,f592])).
% 1.29/0.53  fof(f592,plain,(
% 1.29/0.53    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f585])).
% 1.29/0.53  % (23940)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.29/0.53  fof(f585,plain,(
% 1.29/0.53    k1_xboole_0 = k10_relat_1(sK1,sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.29/0.53    inference(backward_demodulation,[],[f341,f559])).
% 1.29/0.53  fof(f341,plain,(
% 1.29/0.53    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.29/0.53    inference(resolution,[],[f168,f91])).
% 1.29/0.53  fof(f91,plain,(
% 1.29/0.53    ( ! [X1] : (~r2_hidden(X1,k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0)) )),
% 1.29/0.53    inference(resolution,[],[f88,f43])).
% 1.29/0.53  fof(f88,plain,(
% 1.29/0.53    ( ! [X0] : (r1_xboole_0(X0,k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0)) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f86,f36])).
% 1.29/0.53  fof(f86,plain,(
% 1.29/0.53    ( ! [X0] : (~r2_hidden(sK2(X0,k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0) | r1_xboole_0(X0,k10_relat_1(sK1,sK0))) )),
% 1.29/0.53    inference(resolution,[],[f71,f56])).
% 1.29/0.53  fof(f71,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1,sK1),sK0) | ~r2_hidden(X0,k10_relat_1(sK1,X1)) | k1_xboole_0 = k10_relat_1(sK1,sK0)) )),
% 1.29/0.53    inference(resolution,[],[f62,f54])).
% 1.29/0.53  fof(f54,plain,(
% 1.29/0.53    r1_xboole_0(sK0,k2_relat_1(sK1)) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.29/0.53    inference(resolution,[],[f32,f38])).
% 1.29/0.53  fof(f38,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f12])).
% 1.29/0.53  fof(f12,plain,(
% 1.29/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f1])).
% 1.29/0.53  fof(f1,axiom,(
% 1.29/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f62,plain,(
% 1.29/0.53    ( ! [X4,X2,X3] : (~r1_xboole_0(X4,k2_relat_1(sK1)) | ~r2_hidden(X2,k10_relat_1(sK1,X3)) | ~r2_hidden(sK6(X2,X3,sK1),X4)) )),
% 1.29/0.53    inference(resolution,[],[f60,f37])).
% 1.29/0.53  fof(f60,plain,(
% 1.29/0.53    ( ! [X4,X3] : (r2_hidden(sK6(X3,X4,sK1),k2_relat_1(sK1)) | ~r2_hidden(X3,k10_relat_1(sK1,X4))) )),
% 1.29/0.53    inference(resolution,[],[f50,f48])).
% 1.29/0.53  fof(f48,plain,(
% 1.29/0.53    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 1.29/0.53    inference(equality_resolution,[],[f40])).
% 1.29/0.53  fof(f40,plain,(
% 1.29/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.29/0.53    inference(cnf_transformation,[],[f26])).
% 1.29/0.53  fof(f50,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK6(X0,X1,sK1)),sK1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 1.29/0.53    inference(resolution,[],[f31,f45])).
% 1.29/0.53  fof(f45,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f30])).
% 1.29/0.53  fof(f827,plain,(
% 1.29/0.53    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f31,f606,f605,f721,f47])).
% 1.29/0.53  fof(f47,plain,(
% 1.29/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f30])).
% 1.29/0.53  fof(f721,plain,(
% 1.29/0.53    r2_hidden(k4_tarski(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1)),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f605,f49])).
% 1.29/0.53  fof(f49,plain,(
% 1.29/0.53    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)) )),
% 1.29/0.53    inference(equality_resolution,[],[f39])).
% 1.29/0.53  fof(f39,plain,(
% 1.29/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.29/0.53    inference(cnf_transformation,[],[f26])).
% 1.29/0.53  fof(f605,plain,(
% 1.29/0.53    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f603,f35])).
% 1.29/0.53  fof(f35,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f20])).
% 1.29/0.53  fof(f603,plain,(
% 1.29/0.53    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.29/0.53    inference(trivial_inequality_removal,[],[f602])).
% 1.29/0.53  fof(f602,plain,(
% 1.29/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.29/0.53    inference(backward_demodulation,[],[f33,f592])).
% 1.29/0.53  fof(f33,plain,(
% 1.29/0.53    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f606,plain,(
% 1.29/0.53    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)),
% 1.29/0.53    inference(unit_resulting_resolution,[],[f603,f36])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (23945)------------------------------
% 1.29/0.53  % (23945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (23945)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (23945)Memory used [KB]: 6652
% 1.29/0.53  % (23945)Time elapsed: 0.091 s
% 1.29/0.53  % (23945)------------------------------
% 1.29/0.53  % (23945)------------------------------
% 1.29/0.53  % (23941)Refutation not found, incomplete strategy% (23941)------------------------------
% 1.29/0.53  % (23941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (23941)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (23941)Memory used [KB]: 10618
% 1.29/0.53  % (23941)Time elapsed: 0.118 s
% 1.29/0.53  % (23941)------------------------------
% 1.29/0.53  % (23941)------------------------------
% 1.29/0.53  % (23929)Success in time 0.156 s
%------------------------------------------------------------------------------
