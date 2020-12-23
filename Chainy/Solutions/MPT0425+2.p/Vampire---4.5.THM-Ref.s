%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0425+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 35.97s
% Output     : Refutation 35.97s
% Verified   : 
% Statistics : Number of formulae       :   39 (  62 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 179 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31780,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31683,f31777])).

fof(f31777,plain,(
    ~ spl32_256 ),
    inference(avatar_contradiction_clause,[],[f31776])).

fof(f31776,plain,
    ( $false
    | ~ spl32_256 ),
    inference(subsumption_resolution,[],[f31775,f891])).

fof(f891,plain,(
    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f780])).

fof(f780,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK0))
    & ! [X3] :
        ( r1_xboole_0(X3,sK2)
        | ~ r2_hidden(X3,sK1) )
    & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f624,f779])).

fof(f779,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,k3_tarski(X0))
        & ! [X3] :
            ( r1_xboole_0(X3,X2)
            | ~ r2_hidden(X3,X1) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
   => ( ~ r1_tarski(sK2,k3_tarski(sK0))
      & ! [X3] :
          ( r1_xboole_0(X3,sK2)
          | ~ r2_hidden(X3,sK1) )
      & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f624,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(flattening,[],[f623])).

fof(f623,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(ennf_transformation,[],[f612])).

fof(f612,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r1_xboole_0(X3,X2) )
          & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
       => r1_tarski(X2,k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f611])).

fof(f611,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
     => r1_tarski(X2,k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_setfam_1)).

fof(f31775,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl32_256 ),
    inference(forward_demodulation,[],[f31751,f1000])).

fof(f1000,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f445])).

fof(f445,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f31751,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | ~ spl32_256 ),
    inference(resolution,[],[f30515,f1291])).

fof(f1291,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,X0)
      | ~ r1_tarski(sK2,k2_xboole_0(k3_tarski(sK0),X0)) ) ),
    inference(resolution,[],[f893,f909])).

fof(f909,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f643])).

fof(f643,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f642])).

fof(f642,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f141])).

fof(f141,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f893,plain,(
    ~ r1_tarski(sK2,k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f780])).

fof(f30515,plain,
    ( r1_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl32_256 ),
    inference(avatar_component_clause,[],[f30514])).

fof(f30514,plain,
    ( spl32_256
  <=> r1_xboole_0(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_256])])).

fof(f31683,plain,(
    spl32_256 ),
    inference(avatar_contradiction_clause,[],[f31682])).

fof(f31682,plain,
    ( $false
    | spl32_256 ),
    inference(subsumption_resolution,[],[f31662,f31661])).

fof(f31661,plain,
    ( ~ r2_hidden(sK18(sK1,sK2),sK1)
    | spl32_256 ),
    inference(resolution,[],[f31381,f1548])).

fof(f1548,plain,(
    ! [X66] :
      ( r1_xboole_0(k3_tarski(X66),sK2)
      | ~ r2_hidden(sK18(X66,sK2),sK1) ) ),
    inference(resolution,[],[f892,f995])).

fof(f995,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ~ r1_xboole_0(sK18(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f818])).

fof(f818,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f693,f817])).

fof(f817,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK18(X0,X1),X1)
        & r2_hidden(sK18(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f693,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f447])).

fof(f447,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f892,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f780])).

fof(f31381,plain,
    ( ~ r1_xboole_0(k3_tarski(sK1),sK2)
    | spl32_256 ),
    inference(resolution,[],[f30516,f933])).

fof(f933,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f663])).

fof(f663,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f30516,plain,
    ( ~ r1_xboole_0(sK2,k3_tarski(sK1))
    | spl32_256 ),
    inference(avatar_component_clause,[],[f30514])).

fof(f31662,plain,
    ( r2_hidden(sK18(sK1,sK2),sK1)
    | spl32_256 ),
    inference(resolution,[],[f31381,f994])).

fof(f994,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK18(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f818])).
%------------------------------------------------------------------------------
