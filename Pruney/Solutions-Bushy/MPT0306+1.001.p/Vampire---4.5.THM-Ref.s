%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0306+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 110 expanded)
%              Number of leaves         :    5 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 288 expanded)
%              Number of equality atoms :   12 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f90,f148])).

fof(f148,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f33,f125,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f125,plain,
    ( r2_hidden(sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2))
    | spl9_2 ),
    inference(forward_demodulation,[],[f120,f99])).

fof(f99,plain,
    ( sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) = k4_tarski(sK4(sK0,sK2,sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),sK5(sK0,sK2,sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f92,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK4(X0,X1,X3),sK5(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK4(X0,X1,X3),sK5(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f92,plain,
    ( r2_hidden(sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK0,sK2))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f33,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f120,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,sK2,sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),sK5(sK0,sK2,sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)))),k2_zfmisc_1(sK1,sK2))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f98,f105,f21])).

fof(f21,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f105,plain,
    ( r2_hidden(sK4(sK0,sK2,sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),sK1)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f8,f97,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,
    ( r2_hidden(sK4(sK0,sK2,sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),sK0)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f92,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
          & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f98,plain,
    ( r2_hidden(sK5(sK0,sK2,sK8(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f92,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl9_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f90,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f29,f67,f19])).

fof(f67,plain,
    ( r2_hidden(sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK1))
    | spl9_1 ),
    inference(forward_demodulation,[],[f64,f41])).

fof(f41,plain,
    ( sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) = k4_tarski(sK4(sK2,sK0,sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),sK5(sK2,sK0,sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f36,f22])).

fof(f36,plain,
    ( r2_hidden(sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)),k2_zfmisc_1(sK2,sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f29,f18])).

fof(f64,plain,
    ( r2_hidden(k4_tarski(sK4(sK2,sK0,sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),sK5(sK2,sK0,sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)))),k2_zfmisc_1(sK2,sK1))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f39,f51,f21])).

fof(f51,plain,
    ( r2_hidden(sK5(sK2,sK0,sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f8,f40,f17])).

fof(f40,plain,
    ( r2_hidden(sK5(sK2,sK0,sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),sK0)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f36,f23])).

fof(f39,plain,
    ( r2_hidden(sK4(sK2,sK0,sK8(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))),sK2)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f36,f24])).

fof(f29,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl9_1
  <=> r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f34,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f7,f31,f27])).

fof(f7,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK2))
    | ~ r1_tarski(k2_zfmisc_1(sK2,sK0),k2_zfmisc_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
