%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t49_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 578 expanded)
%              Number of leaves         :   39 ( 162 expanded)
%              Depth                    :   19
%              Number of atoms          :  586 (1789 expanded)
%              Number of equality atoms :  183 ( 851 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13725,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f175,f328,f356,f386,f2322,f2361,f2374,f2570,f2574,f3354,f3437,f3486,f13462,f13722])).

fof(f13722,plain,
    ( ~ spl5_0
    | spl5_97
    | spl5_99
    | spl5_209 ),
    inference(avatar_contradiction_clause,[],[f13721])).

fof(f13721,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_97
    | ~ spl5_99
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f13719,f103])).

fof(f103,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_0
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f13719,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_0
    | ~ spl5_97
    | ~ spl5_99
    | ~ spl5_209 ),
    inference(resolution,[],[f13714,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t3_subset)).

fof(f13714,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))
    | ~ spl5_0
    | ~ spl5_97
    | ~ spl5_99
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f13712,f58])).

fof(f58,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != sK0
    & ( r1_tarski(sK0,k3_zfmisc_1(sK2,sK0,sK1))
      | r1_tarski(sK0,k3_zfmisc_1(sK1,sK2,sK0))
      | r1_tarski(sK0,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & ( r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) )
   => ( k1_xboole_0 != sK0
      & ( r1_tarski(sK0,k3_zfmisc_1(sK2,sK0,sK1))
        | r1_tarski(sK0,k3_zfmisc_1(sK1,sK2,sK0))
        | r1_tarski(sK0,k3_zfmisc_1(sK0,sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & ( r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        | r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        | r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
            & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
            & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t49_mcart_1)).

fof(f13712,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))
    | k1_xboole_0 = sK0
    | ~ spl5_0
    | ~ spl5_97
    | ~ spl5_99
    | ~ spl5_209 ),
    inference(resolution,[],[f13710,f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f76,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t29_mcart_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t4_subset)).

fof(f13710,plain,
    ( ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_0
    | ~ spl5_97
    | ~ spl5_99
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f13709,f2203])).

fof(f2203,plain,
    ( k1_xboole_0 != sK2
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f2202])).

fof(f2202,plain,
    ( spl5_97
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f13709,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_0
    | ~ spl5_99
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f13705,f2209])).

fof(f2209,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f2208])).

fof(f2208,plain,
    ( spl5_99
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f13705,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_0
    | ~ spl5_209 ),
    inference(resolution,[],[f13689,f3705])).

fof(f3705,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) )
    | ~ spl5_0 ),
    inference(subsumption_resolution,[],[f3697,f58])).

fof(f3697,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
        | k1_xboole_0 = sK0 )
    | ~ spl5_0 ),
    inference(resolution,[],[f103,f924])).

fof(f924,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f206,f72])).

fof(f206,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k1_xboole_0 = X1
      | r2_hidden(X3,X2)
      | ~ m1_subset_1(X3,X2) ) ),
    inference(resolution,[],[f179,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t2_subset)).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f82,f62])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t5_subset)).

fof(f13689,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
        | k1_xboole_0 = X2
        | k1_xboole_0 = X3 )
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f13688,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t1_subset)).

fof(f13688,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | ~ r2_hidden(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) )
    | ~ spl5_209 ),
    inference(subsumption_resolution,[],[f13685,f58])).

fof(f13685,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
        | k1_xboole_0 = sK0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | ~ r2_hidden(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) )
    | ~ spl5_209 ),
    inference(duplicate_literal_removal,[],[f13680])).

fof(f13680,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3))
        | k1_xboole_0 = sK0
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = sK0
        | ~ r2_hidden(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,X2),X3)) )
    | ~ spl5_209 ),
    inference(resolution,[],[f13526,f1690])).

fof(f1690,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k5_mcart_1(X5,X6,X7,sK3(X4)),X4)
      | k1_xboole_0 = X4
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | ~ r2_hidden(sK3(X4),k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)) ) ),
    inference(resolution,[],[f822,f67])).

fof(f822,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3(X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X3
      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,sK3(X3)),X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f703])).

fof(f703,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( sK3(X9) != X8
      | ~ r2_hidden(k5_mcart_1(X5,X6,X7,X8),X9)
      | k1_xboole_0 = X9
      | ~ m1_subset_1(X8,k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7))
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5 ) ),
    inference(superposition,[],[f63,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f81,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',d3_zfmisc_1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t48_mcart_1)).

fof(f63,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK3(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13526,plain,
    ( ! [X2,X3,X1] :
        ( r2_hidden(k5_mcart_1(sK0,X1,X2,X3),sK0)
        | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2)) )
    | ~ spl5_209 ),
    inference(resolution,[],[f13519,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f84,f75])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',dt_k5_mcart_1)).

fof(f13519,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | r2_hidden(X0,sK0) )
    | ~ spl5_209 ),
    inference(resolution,[],[f3689,f68])).

fof(f3689,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_209 ),
    inference(avatar_component_clause,[],[f3688])).

fof(f3688,plain,
    ( spl5_209
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f13462,plain,(
    ~ spl5_208 ),
    inference(avatar_contradiction_clause,[],[f13461])).

fof(f13461,plain,
    ( $false
    | ~ spl5_208 ),
    inference(subsumption_resolution,[],[f13433,f58])).

fof(f13433,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_208 ),
    inference(resolution,[],[f3686,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t6_boole)).

fof(f3686,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_208 ),
    inference(avatar_component_clause,[],[f3685])).

fof(f3685,plain,
    ( spl5_208
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f3486,plain,
    ( ~ spl5_0
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f3485])).

fof(f3485,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f3470,f58])).

fof(f3470,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_0
    | ~ spl5_22 ),
    inference(resolution,[],[f396,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t3_xboole_1)).

fof(f396,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl5_0
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f349,f103])).

fof(f349,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl5_22
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f3437,plain,
    ( ~ spl5_20
    | ~ spl5_96 ),
    inference(avatar_contradiction_clause,[],[f3436])).

fof(f3436,plain,
    ( $false
    | ~ spl5_20
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f3435,f118])).

fof(f118,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f117,f59])).

fof(f59,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',dt_o_0_0_xboole_0)).

fof(f117,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f60,f59])).

fof(f3435,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_96 ),
    inference(forward_demodulation,[],[f3434,f126])).

fof(f126,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X2) ),
    inference(superposition,[],[f96,f95])).

fof(f95,plain,(
    ! [X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f80,f75])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t35_mcart_1)).

fof(f96,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f79,f75])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f3434,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl5_20
    | ~ spl5_96 ),
    inference(forward_demodulation,[],[f3433,f126])).

fof(f3433,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0),sK1))
    | ~ spl5_20
    | ~ spl5_96 ),
    inference(forward_demodulation,[],[f570,f2206])).

fof(f2206,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f2205])).

fof(f2205,plain,
    ( spl5_96
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f570,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl5_20 ),
    inference(resolution,[],[f327,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t7_boole)).

fof(f327,plain,
    ( r2_hidden(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl5_20
  <=> r2_hidden(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f3354,plain,
    ( ~ spl5_24
    | ~ spl5_96 ),
    inference(avatar_contradiction_clause,[],[f3353])).

fof(f3353,plain,
    ( $false
    | ~ spl5_24
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f3352,f118])).

fof(f3352,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_24
    | ~ spl5_96 ),
    inference(forward_demodulation,[],[f3351,f627])).

fof(f627,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ),
    inference(condensation,[],[f626])).

fof(f626,plain,(
    ! [X4,X2] :
      ( k1_xboole_0 = X4
      | k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f625,f126])).

fof(f625,plain,(
    ! [X4,X2] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4)
      | k1_xboole_0 = X4
      | k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ) ),
    inference(condensation,[],[f621])).

fof(f621,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4)
      | k1_xboole_0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f90,f96])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f3351,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k1_xboole_0))
    | ~ spl5_24
    | ~ spl5_96 ),
    inference(forward_demodulation,[],[f434,f2206])).

fof(f434,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_24 ),
    inference(resolution,[],[f355,f74])).

fof(f355,plain,
    ( r2_hidden(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl5_24
  <=> r2_hidden(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f2574,plain,
    ( spl5_23
    | ~ spl5_98 ),
    inference(avatar_contradiction_clause,[],[f2573])).

fof(f2573,plain,
    ( $false
    | ~ spl5_23
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2572,f126])).

fof(f2572,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)
    | ~ spl5_23
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f2387,f627])).

fof(f2387,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | ~ spl5_23
    | ~ spl5_98 ),
    inference(backward_demodulation,[],[f2212,f346])).

fof(f346,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl5_23
  <=> k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f2212,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f2211])).

fof(f2211,plain,
    ( spl5_98
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f2570,plain,
    ( spl5_19
    | ~ spl5_98 ),
    inference(avatar_contradiction_clause,[],[f2569])).

fof(f2569,plain,
    ( $false
    | ~ spl5_19
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2385,f627])).

fof(f2385,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),k1_xboole_0)
    | ~ spl5_19
    | ~ spl5_98 ),
    inference(backward_demodulation,[],[f2212,f318])).

fof(f318,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl5_19
  <=> k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f2374,plain,
    ( ~ spl5_120
    | spl5_129 ),
    inference(avatar_contradiction_clause,[],[f2373])).

fof(f2373,plain,
    ( $false
    | ~ spl5_120
    | ~ spl5_129 ),
    inference(subsumption_resolution,[],[f2372,f58])).

fof(f2372,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_120
    | ~ spl5_129 ),
    inference(subsumption_resolution,[],[f2371,f2291])).

fof(f2291,plain,
    ( m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f2290])).

fof(f2290,plain,
    ( spl5_120
  <=> m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f2371,plain,
    ( ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | k1_xboole_0 = sK0
    | ~ spl5_129 ),
    inference(resolution,[],[f2360,f444])).

fof(f444,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_hidden(k6_mcart_1(X4,X5,X6,X3),X5)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X4,X5),X6))
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f92,f139])).

fof(f139,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,X4)
      | r2_hidden(X3,X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f68,f60])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f83,f75])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',dt_k6_mcart_1)).

fof(f2360,plain,
    ( ~ r2_hidden(k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),sK0)
    | ~ spl5_129 ),
    inference(avatar_component_clause,[],[f2359])).

fof(f2359,plain,
    ( spl5_129
  <=> ~ r2_hidden(k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f2361,plain,
    ( spl5_96
    | spl5_98
    | ~ spl5_129
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f2354,f2290,f2359,f2211,f2205])).

fof(f2354,plain,
    ( ~ r2_hidden(k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl5_120 ),
    inference(subsumption_resolution,[],[f2344,f58])).

fof(f2344,plain,
    ( k1_xboole_0 = sK0
    | ~ r2_hidden(k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl5_120 ),
    inference(duplicate_literal_removal,[],[f2339])).

fof(f2339,plain,
    ( k1_xboole_0 = sK0
    | ~ r2_hidden(k6_mcart_1(sK2,sK0,sK1,sK3(sK0)),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl5_120 ),
    inference(resolution,[],[f2291,f764])).

fof(f764,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3(X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X3
      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,sK3(X3)),X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f702])).

fof(f702,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK3(X4) != X3
      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X3),X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f64,f91])).

fof(f64,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2322,plain,
    ( ~ spl5_4
    | spl5_121 ),
    inference(avatar_contradiction_clause,[],[f2321])).

fof(f2321,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f2319,f115])).

fof(f115,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_4
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2319,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl5_121 ),
    inference(resolution,[],[f2314,f72])).

fof(f2314,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)))
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f2311,f58])).

fof(f2311,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)))
    | k1_xboole_0 = sK0
    | ~ spl5_121 ),
    inference(resolution,[],[f2294,f218])).

fof(f2294,plain,
    ( ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f2293])).

fof(f2293,plain,
    ( spl5_121
  <=> ~ m1_subset_1(sK3(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f386,plain,
    ( ~ spl5_4
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f382,f58])).

fof(f382,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(resolution,[],[f364,f61])).

fof(f364,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f321,f115])).

fof(f321,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl5_18
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f356,plain,
    ( spl5_22
    | spl5_24
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f343,f102,f354,f348])).

fof(f343,plain,
    ( r2_hidden(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_0 ),
    inference(resolution,[],[f331,f139])).

fof(f331,plain,
    ( m1_subset_1(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_0 ),
    inference(subsumption_resolution,[],[f329,f58])).

fof(f329,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_0 ),
    inference(resolution,[],[f103,f307])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | m1_subset_1(sK4(X0),X1) ) ),
    inference(resolution,[],[f219,f72])).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | m1_subset_1(sK4(X2),X3)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f76,f180])).

fof(f180,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f139,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',existence_m1_subset_1)).

fof(f328,plain,
    ( spl5_18
    | spl5_20
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f315,f114,f326,f320])).

fof(f315,plain,
    ( r2_hidden(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f314,f139])).

fof(f314,plain,
    ( m1_subset_1(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f313,f58])).

fof(f313,plain,
    ( k1_xboole_0 = sK0
    | m1_subset_1(sK4(sK0),k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f307,f115])).

fof(f175,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f169,f58])).

fof(f169,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(resolution,[],[f70,f109])).

fof(f109,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_2
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t49_mcart_1.p',t135_zfmisc_1)).

fof(f116,plain,
    ( spl5_0
    | spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f86,f114,f108,f102])).

fof(f86,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK0),sK1))
    | r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK0))
    | r1_tarski(sK0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f57,f75,f75,f75])).

fof(f57,plain,
    ( r1_tarski(sK0,k3_zfmisc_1(sK2,sK0,sK1))
    | r1_tarski(sK0,k3_zfmisc_1(sK1,sK2,sK0))
    | r1_tarski(sK0,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
