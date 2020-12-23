%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t74_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:13 EDT 2019

% Result     : Theorem 7.66s
% Output     : Refutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 108 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   19
%              Number of atoms          :  181 ( 371 expanded)
%              Number of equality atoms :   35 ( 102 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f168,f273])).

fof(f273,plain,(
    ~ spl14_0 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl14_0 ),
    inference(unit_resulting_resolution,[],[f53,f135])).

fof(f135,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) = sK0
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl14_0
  <=> k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f53,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) != sK0 ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t74_mcart_1.p',d3_zfmisc_1)).

fof(f34,plain,(
    k3_zfmisc_1(sK1,sK2,sK3) != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_zfmisc_1(X1,X2,X3) != X0
      & ! [X4] :
          ( r2_hidden(X4,X0)
        <=> ? [X5,X6,X7] :
              ( k3_mcart_1(X5,X6,X7) = X4
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ! [X4] :
            ( r2_hidden(X4,X0)
          <=> ? [X5,X6,X7] :
                ( k3_mcart_1(X5,X6,X7) = X4
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) ) )
       => k3_zfmisc_1(X1,X2,X3) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( r2_hidden(X4,X0)
        <=> ? [X5,X6,X7] :
              ( k3_mcart_1(X5,X6,X7) = X4
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) ) )
     => k3_zfmisc_1(X1,X2,X3) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t74_mcart_1.p',t74_mcart_1)).

fof(f168,plain,(
    ~ spl14_2 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl14_2 ),
    inference(unit_resulting_resolution,[],[f53,f141,f141,f85])).

fof(f85,plain,(
    ! [X7] :
      ( ~ r2_hidden(sK7(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),sK0)
      | ~ r2_hidden(sK7(X7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),X7)
      | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) = X7 ) ),
    inference(resolution,[],[f79,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | ~ r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t74_mcart_1.p',t2_tarski)).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f77,f29])).

fof(f29,plain,(
    ! [X4] :
      ( r2_hidden(sK4(X4),sK1)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0),X1)
      | r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK2),sK3))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK2),sK3))
      | ~ r2_hidden(sK4(X0),X1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f75,f30])).

fof(f30,plain,(
    ! [X4] :
      ( r2_hidden(sK5(X4),sK2)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0),X2)
      | ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK3))
      | ~ r2_hidden(sK4(X0),X1) ) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t74_mcart_1.p',d2_zfmisc_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X1)
      | r2_hidden(X0,k2_zfmisc_1(X1,sK3))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,sK3))
      | ~ r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X1)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f65,f31])).

fof(f31,plain,(
    ! [X4] :
      ( r2_hidden(sK6(X4),sK3)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0),X2)
      | r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f58,f55])).

fof(f55,plain,(
    ! [X4] :
      ( k4_tarski(k4_tarski(sK4(X4),sK5(X4)),sK6(X4)) = X4
      | ~ r2_hidden(X4,sK0) ) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t74_mcart_1.p',d3_mcart_1)).

fof(f32,plain,(
    ! [X4] :
      ( k3_mcart_1(sK4(X4),sK5(X4),sK6(X4)) = X4
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f141,plain,
    ( r2_hidden(sK7(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl14_2
  <=> r2_hidden(sK7(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f142,plain,
    ( spl14_0
    | spl14_2 ),
    inference(avatar_split_clause,[],[f128,f140,f134])).

fof(f128,plain,
    ( r2_hidden(sK7(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),sK0)
    | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) = sK0 ),
    inference(factoring,[],[f107])).

fof(f107,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),sK0)
      | r2_hidden(sK7(X3,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)),X3)
      | k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) = X3 ) ),
    inference(resolution,[],[f103,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | r2_hidden(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(resolution,[],[f101,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X1,sK3,X0),k2_zfmisc_1(sK1,sK2))
      | r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(sK9(X1,sK3,X0),k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK3)) ) ),
    inference(resolution,[],[f95,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1,X2),sK3)
      | r2_hidden(X2,sK0)
      | ~ r2_hidden(sK9(X0,X1,X2),k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f92,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(k4_tarski(X1,X0),sK0)
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X1,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f90,f61])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(X2,sK2,X0),sK1)
      | ~ r2_hidden(X1,sK3)
      | r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2)) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(sK9(X2,sK2,X0),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK2)) ) ),
    inference(resolution,[],[f67,f60])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK10(X0,X1,X2),sK2)
      | r2_hidden(k4_tarski(X2,X3),sK0)
      | ~ r2_hidden(X3,sK3)
      | ~ r2_hidden(sK9(X0,X1,X2),sK1)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f56,f59])).

fof(f56,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(k4_tarski(k4_tarski(X5,X6),X7),sK0)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | k4_tarski(k4_tarski(X5,X6),X7) != X4
      | r2_hidden(X4,sK0) ) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f33,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | k3_mcart_1(X5,X6,X7) != X4
      | r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
