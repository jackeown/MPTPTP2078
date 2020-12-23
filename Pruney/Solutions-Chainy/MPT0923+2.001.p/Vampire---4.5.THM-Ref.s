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
% DateTime   : Thu Dec  3 12:59:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  79 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   27
%              Number of atoms          :  238 ( 366 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :   22 (  11 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f25,f27,f27,f27,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X1,sK3))
      | ~ r1_tarski(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK0,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,sK4)) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r1_tarski(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X1,sK3))
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,sK4))
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,sK4)) ) ),
    inference(condensation,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r1_tarski(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X1,sK3))
      | ~ r1_tarski(X0,k2_zfmisc_1(X2,sK4))
      | ~ r2_hidden(sK0,X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(X2,sK4)) ) ),
    inference(resolution,[],[f48,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X1,sK4,sK0),X2)
      | ~ r2_hidden(sK0,X0)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,sK4)) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r2_hidden(sK5(X1,sK4,sK0),X2)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,sK4))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,sK4)) ) ),
    inference(condensation,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,sK4,sK0),X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X1,k2_zfmisc_1(X2,sK3))
      | ~ r2_hidden(sK0,X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(X0,sK4))
      | ~ r2_hidden(sK0,X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X0,sK4)) ) ),
    inference(resolution,[],[f45,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK6(X0,X1,sK0),sK4)
      | ~ r2_hidden(sK5(X0,X1,sK0),X2)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3))
      | ~ r2_hidden(sK0,X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK0),X2)
      | ~ r2_hidden(sK6(X0,X1,sK0),sK4)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3))
      | ~ r2_hidden(sK0,X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X0,X1))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3)) ) ),
    inference(condensation,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK0),X2)
      | ~ r2_hidden(sK6(X0,X1,sK0),sK4)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3))
      | ~ r2_hidden(sK0,X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK5(X0,X1,sK0),X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X3,sK3)) ) ),
    inference(resolution,[],[f42,f20])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK5(X3,sK3,sK5(X0,X1,sK0)),X4)
      | ~ r2_hidden(sK5(X0,X1,sK0),X2)
      | ~ r2_hidden(sK6(X0,X1,sK0),sK4)
      | ~ r1_tarski(X4,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3))
      | ~ r2_hidden(sK0,X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK0),X2)
      | ~ r2_hidden(sK5(X3,sK3,sK5(X0,X1,sK0)),X4)
      | ~ r2_hidden(sK6(X0,X1,sK0),sK4)
      | ~ r1_tarski(X4,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3))
      | ~ r2_hidden(sK0,X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X0,X1))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,sK3)) ) ),
    inference(condensation,[],[f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK5(X0,sK3,sK5(X1,X2,sK0)),X3)
      | ~ r2_hidden(sK6(X1,X2,sK0),sK4)
      | ~ r1_tarski(X3,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK5(X1,X2,sK0),X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X0,sK3))
      | ~ r2_hidden(sK0,X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK5(X1,X2,sK0),X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X0,sK3)) ) ),
    inference(resolution,[],[f39,f21])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3)
      | ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4)
      | ~ r2_hidden(sK6(X2,X3,sK0),sK4)
      | ~ r1_tarski(X4,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK5(X2,X3,sK0),X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4)
      | ~ r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3)
      | ~ r2_hidden(sK6(X2,X3,sK0),sK4)
      | ~ r1_tarski(X4,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK5(X2,X3,sK0),X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X2,X3))
      | ~ r1_tarski(X4,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(condensation,[],[f37])).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3)
      | ~ r2_hidden(sK6(X2,X3,sK0),sK4)
      | ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(sK5(X2,X3,sK0),X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f36,f20])).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(sK5(X5,sK2,sK5(X0,X1,sK5(X2,X3,sK0))),sK1)
      | ~ r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3)
      | ~ r2_hidden(sK6(X2,X3,sK0),sK4)
      | ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4)
      | ~ r1_tarski(X4,k2_zfmisc_1(X5,sK2))
      | ~ r2_hidden(sK5(X2,X3,sK0),X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4)
      | ~ r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3)
      | ~ r2_hidden(sK6(X2,X3,sK0),sK4)
      | ~ r2_hidden(sK5(X5,sK2,sK5(X0,X1,sK5(X2,X3,sK0))),sK1)
      | ~ r1_tarski(X4,k2_zfmisc_1(X5,sK2))
      | ~ r2_hidden(sK5(X2,X3,sK0),X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(X2,X3))
      | ~ r1_tarski(X4,k2_zfmisc_1(X5,sK2)) ) ),
    inference(condensation,[],[f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3)
      | ~ r2_hidden(sK6(X2,X3,sK0),sK4)
      | ~ r2_hidden(sK5(X4,sK2,sK5(X0,X1,sK5(X2,X3,sK0))),sK1)
      | ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X4,sK2))
      | ~ r2_hidden(sK5(X2,X3,sK0),X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK0,X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X8)
      | ~ r1_tarski(X8,k2_zfmisc_1(X4,sK2)) ) ),
    inference(resolution,[],[f33,f21])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ r2_hidden(sK6(X0,X1,sK5(X2,X3,sK5(X4,X5,sK0))),sK2)
      | ~ r2_hidden(sK6(X2,X3,sK5(X4,X5,sK0)),sK3)
      | ~ r2_hidden(sK6(X4,X5,sK0),sK4)
      | ~ r2_hidden(sK5(X0,X1,sK5(X2,X3,sK5(X4,X5,sK0))),sK1)
      | ~ r2_hidden(sK5(X2,X3,sK5(X4,X5,sK0)),X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK5(X4,X5,sK0),X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(sK0,X8)
      | ~ r1_tarski(X8,k2_zfmisc_1(X4,X5)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( sK0 != X2
      | ~ r2_hidden(sK6(X3,X4,sK5(X5,X6,sK5(X0,X1,X2))),sK2)
      | ~ r2_hidden(sK6(X5,X6,sK5(X0,X1,X2)),sK3)
      | ~ r2_hidden(sK6(X0,X1,X2),sK4)
      | ~ r2_hidden(sK5(X3,X4,sK5(X5,X6,sK5(X0,X1,X2))),sK1)
      | ~ r2_hidden(sK5(X5,X6,sK5(X0,X1,X2)),X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(sK5(X0,X1,X2),X8)
      | ~ r1_tarski(X8,k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(X2,X9)
      | ~ r1_tarski(X9,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f31,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sK0 != k4_tarski(X2,X3)
      | ~ r2_hidden(sK6(X4,X5,sK5(X0,X1,X2)),sK2)
      | ~ r2_hidden(sK6(X0,X1,X2),sK3)
      | ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(sK5(X4,X5,sK5(X0,X1,X2)),sK1)
      | ~ r2_hidden(sK5(X0,X1,X2),X6)
      | ~ r1_tarski(X6,k2_zfmisc_1(X4,X5))
      | ~ r2_hidden(X2,X7)
      | ~ r1_tarski(X7,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f30,f22])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK0 != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(sK6(X0,X1,X2),sK2)
      | ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(X4,sK4)
      | ~ r2_hidden(sK5(X0,X1,X2),sK1)
      | ~ r2_hidden(X2,X5)
      | ~ r1_tarski(X5,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f26,f22])).

fof(f26,plain,(
    ! [X6,X8,X7,X5] :
      ( sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f11,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f18,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f11,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | k4_mcart_1(X5,X6,X7,X8) != sK0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f27,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f25,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f12,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f12,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (17091)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (17083)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (17091)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (17106)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (17081)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f25,f27,f27,f27,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X1,sK3)) | ~r1_tarski(X1,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK0,X0) | ~r1_tarski(X0,k2_zfmisc_1(X2,sK4))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK0,X0) | ~r1_tarski(X1,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X1,sK3)) | ~r1_tarski(X0,k2_zfmisc_1(X2,sK4)) | ~r1_tarski(X0,k2_zfmisc_1(X2,sK4))) )),
% 0.20/0.51    inference(condensation,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK0,X0) | ~r1_tarski(X1,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X1,sK3)) | ~r1_tarski(X0,k2_zfmisc_1(X2,sK4)) | ~r2_hidden(sK0,X3) | ~r1_tarski(X3,k2_zfmisc_1(X2,sK4))) )),
% 0.20/0.51    inference(resolution,[],[f48,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X1,X2,X3),X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK5(X1,sK4,sK0),X2) | ~r2_hidden(sK0,X0) | ~r1_tarski(X3,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,sK4))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK0,X0) | ~r2_hidden(sK5(X1,sK4,sK0),X2) | ~r1_tarski(X3,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,sK4)) | ~r1_tarski(X0,k2_zfmisc_1(X1,sK4))) )),
% 0.20/0.51    inference(condensation,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK5(X0,sK4,sK0),X1) | ~r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X1,k2_zfmisc_1(X2,sK3)) | ~r2_hidden(sK0,X3) | ~r1_tarski(X3,k2_zfmisc_1(X0,sK4)) | ~r2_hidden(sK0,X4) | ~r1_tarski(X4,k2_zfmisc_1(X0,sK4))) )),
% 0.20/0.51    inference(resolution,[],[f45,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X1,X2,X3),X2) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK6(X0,X1,sK0),sK4) | ~r2_hidden(sK5(X0,X1,sK0),X2) | ~r1_tarski(X3,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3)) | ~r2_hidden(sK0,X4) | ~r1_tarski(X4,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK5(X0,X1,sK0),X2) | ~r2_hidden(sK6(X0,X1,sK0),sK4) | ~r1_tarski(X3,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3)) | ~r2_hidden(sK0,X4) | ~r1_tarski(X4,k2_zfmisc_1(X0,X1)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3))) )),
% 0.20/0.51    inference(condensation,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK5(X0,X1,sK0),X2) | ~r2_hidden(sK6(X0,X1,sK0),sK4) | ~r1_tarski(X3,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3)) | ~r2_hidden(sK0,X4) | ~r1_tarski(X4,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK5(X0,X1,sK0),X5) | ~r1_tarski(X5,k2_zfmisc_1(X3,sK3))) )),
% 0.20/0.51    inference(resolution,[],[f42,f20])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK5(X3,sK3,sK5(X0,X1,sK0)),X4) | ~r2_hidden(sK5(X0,X1,sK0),X2) | ~r2_hidden(sK6(X0,X1,sK0),sK4) | ~r1_tarski(X4,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3)) | ~r2_hidden(sK0,X5) | ~r1_tarski(X5,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK5(X0,X1,sK0),X2) | ~r2_hidden(sK5(X3,sK3,sK5(X0,X1,sK0)),X4) | ~r2_hidden(sK6(X0,X1,sK0),sK4) | ~r1_tarski(X4,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3)) | ~r2_hidden(sK0,X5) | ~r1_tarski(X5,k2_zfmisc_1(X0,X1)) | ~r1_tarski(X2,k2_zfmisc_1(X3,sK3))) )),
% 0.20/0.51    inference(condensation,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK5(X0,sK3,sK5(X1,X2,sK0)),X3) | ~r2_hidden(sK6(X1,X2,sK0),sK4) | ~r1_tarski(X3,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK5(X1,X2,sK0),X4) | ~r1_tarski(X4,k2_zfmisc_1(X0,sK3)) | ~r2_hidden(sK0,X5) | ~r1_tarski(X5,k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK5(X1,X2,sK0),X6) | ~r1_tarski(X6,k2_zfmisc_1(X0,sK3))) )),
% 0.20/0.51    inference(resolution,[],[f39,f21])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3) | ~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4) | ~r2_hidden(sK6(X2,X3,sK0),sK4) | ~r1_tarski(X4,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK5(X2,X3,sK0),X5) | ~r1_tarski(X5,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X6) | ~r1_tarski(X6,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4) | ~r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3) | ~r2_hidden(sK6(X2,X3,sK0),sK4) | ~r1_tarski(X4,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK5(X2,X3,sK0),X5) | ~r1_tarski(X5,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X6) | ~r1_tarski(X6,k2_zfmisc_1(X2,X3)) | ~r1_tarski(X4,k2_zfmisc_1(sK1,sK2))) )),
% 0.20/0.51    inference(condensation,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3) | ~r2_hidden(sK6(X2,X3,sK0),sK4) | ~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4) | ~r1_tarski(X4,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(sK5(X2,X3,sK0),X5) | ~r1_tarski(X5,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X6) | ~r1_tarski(X6,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X7) | ~r1_tarski(X7,k2_zfmisc_1(sK1,sK2))) )),
% 0.20/0.51    inference(resolution,[],[f36,f20])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~r2_hidden(sK5(X5,sK2,sK5(X0,X1,sK5(X2,X3,sK0))),sK1) | ~r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3) | ~r2_hidden(sK6(X2,X3,sK0),sK4) | ~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4) | ~r1_tarski(X4,k2_zfmisc_1(X5,sK2)) | ~r2_hidden(sK5(X2,X3,sK0),X6) | ~r1_tarski(X6,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X7) | ~r1_tarski(X7,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X4) | ~r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3) | ~r2_hidden(sK6(X2,X3,sK0),sK4) | ~r2_hidden(sK5(X5,sK2,sK5(X0,X1,sK5(X2,X3,sK0))),sK1) | ~r1_tarski(X4,k2_zfmisc_1(X5,sK2)) | ~r2_hidden(sK5(X2,X3,sK0),X6) | ~r1_tarski(X6,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X7) | ~r1_tarski(X7,k2_zfmisc_1(X2,X3)) | ~r1_tarski(X4,k2_zfmisc_1(X5,sK2))) )),
% 0.20/0.51    inference(condensation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~r2_hidden(sK6(X0,X1,sK5(X2,X3,sK0)),sK3) | ~r2_hidden(sK6(X2,X3,sK0),sK4) | ~r2_hidden(sK5(X4,sK2,sK5(X0,X1,sK5(X2,X3,sK0))),sK1) | ~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X5) | ~r1_tarski(X5,k2_zfmisc_1(X4,sK2)) | ~r2_hidden(sK5(X2,X3,sK0),X6) | ~r1_tarski(X6,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK0,X7) | ~r1_tarski(X7,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK0)),X8) | ~r1_tarski(X8,k2_zfmisc_1(X4,sK2))) )),
% 0.20/0.51    inference(resolution,[],[f33,f21])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~r2_hidden(sK6(X0,X1,sK5(X2,X3,sK5(X4,X5,sK0))),sK2) | ~r2_hidden(sK6(X2,X3,sK5(X4,X5,sK0)),sK3) | ~r2_hidden(sK6(X4,X5,sK0),sK4) | ~r2_hidden(sK5(X0,X1,sK5(X2,X3,sK5(X4,X5,sK0))),sK1) | ~r2_hidden(sK5(X2,X3,sK5(X4,X5,sK0)),X6) | ~r1_tarski(X6,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK5(X4,X5,sK0),X7) | ~r1_tarski(X7,k2_zfmisc_1(X2,X3)) | ~r2_hidden(sK0,X8) | ~r1_tarski(X8,k2_zfmisc_1(X4,X5))) )),
% 0.20/0.51    inference(equality_resolution,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (sK0 != X2 | ~r2_hidden(sK6(X3,X4,sK5(X5,X6,sK5(X0,X1,X2))),sK2) | ~r2_hidden(sK6(X5,X6,sK5(X0,X1,X2)),sK3) | ~r2_hidden(sK6(X0,X1,X2),sK4) | ~r2_hidden(sK5(X3,X4,sK5(X5,X6,sK5(X0,X1,X2))),sK1) | ~r2_hidden(sK5(X5,X6,sK5(X0,X1,X2)),X7) | ~r1_tarski(X7,k2_zfmisc_1(X3,X4)) | ~r2_hidden(sK5(X0,X1,X2),X8) | ~r1_tarski(X8,k2_zfmisc_1(X5,X6)) | ~r2_hidden(X2,X9) | ~r1_tarski(X9,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(superposition,[],[f31,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_tarski(sK5(X1,X2,X3),sK6(X1,X2,X3)) = X3 | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sK0 != k4_tarski(X2,X3) | ~r2_hidden(sK6(X4,X5,sK5(X0,X1,X2)),sK2) | ~r2_hidden(sK6(X0,X1,X2),sK3) | ~r2_hidden(X3,sK4) | ~r2_hidden(sK5(X4,X5,sK5(X0,X1,X2)),sK1) | ~r2_hidden(sK5(X0,X1,X2),X6) | ~r1_tarski(X6,k2_zfmisc_1(X4,X5)) | ~r2_hidden(X2,X7) | ~r1_tarski(X7,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(superposition,[],[f30,f22])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (sK0 != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(sK6(X0,X1,X2),sK2) | ~r2_hidden(X3,sK3) | ~r2_hidden(X4,sK4) | ~r2_hidden(sK5(X0,X1,X2),sK1) | ~r2_hidden(X2,X5) | ~r1_tarski(X5,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(superposition,[],[f26,f22])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X6,X8,X7,X5] : (sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X8,sK4) | ~r2_hidden(X5,sK1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f11,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ( ! [X6,X8,X7,X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X8,sK4) | k4_mcart_1(X5,X6,X7,X8) != sK0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_mcart_1)).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.20/0.51    inference(definition_unfolding,[],[f12,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (17091)------------------------------
% 0.20/0.51  % (17091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17091)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (17091)Memory used [KB]: 6268
% 0.20/0.51  % (17091)Time elapsed: 0.105 s
% 0.20/0.51  % (17091)------------------------------
% 0.20/0.51  % (17091)------------------------------
% 0.20/0.51  % (17077)Success in time 0.153 s
%------------------------------------------------------------------------------
