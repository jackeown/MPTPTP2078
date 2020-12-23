%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0352+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 4.32s
% Output     : Refutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 261 expanded)
%              Number of leaves         :   10 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  157 (1059 expanded)
%              Number of equality atoms :   22 (  72 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5299,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1014,f1015,f1373,f5293])).

fof(f5293,plain,
    ( spl21_1
    | ~ spl21_2 ),
    inference(avatar_contradiction_clause,[],[f5292])).

fof(f5292,plain,
    ( $false
    | spl21_1
    | ~ spl21_2 ),
    inference(subsumption_resolution,[],[f5291,f1009])).

fof(f1009,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl21_1 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1007,plain,
    ( spl21_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_1])])).

fof(f5291,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl21_2 ),
    inference(forward_demodulation,[],[f5290,f2652])).

fof(f2652,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2651,f1047])).

fof(f1047,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1029,f1028])).

fof(f1028,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f695,f700])).

fof(f700,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f498])).

fof(f498,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f457])).

fof(f457,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f695,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f603])).

fof(f603,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f600,f602,f601])).

fof(f601,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f602,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f600,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f599])).

fof(f599,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f496])).

fof(f496,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f490])).

fof(f490,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f489])).

fof(f489,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f1029,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f695,f701])).

fof(f701,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f499])).

fof(f499,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f460])).

fof(f460,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f2651,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | sK1 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2650,f1028])).

fof(f2650,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f2649,f910])).

fof(f910,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2649,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f2645,f1028])).

fof(f2645,plain,
    ( sK1 = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f1027,f700])).

fof(f1027,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f695,f699])).

fof(f699,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f497])).

fof(f497,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f5290,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl21_2 ),
    inference(forward_demodulation,[],[f5289,f910])).

fof(f5289,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl21_2 ),
    inference(forward_demodulation,[],[f5245,f2766])).

fof(f2766,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f2765,f1090])).

fof(f1090,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f1072,f1071])).

fof(f1071,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f696,f700])).

fof(f696,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f603])).

fof(f1072,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f696,f701])).

fof(f2765,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | sK2 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f2764,f1071])).

fof(f2764,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f2763,f910])).

fof(f2763,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f2758,f1071])).

fof(f2758,plain,
    ( sK2 = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f1070,f700])).

fof(f1070,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f696,f699])).

fof(f5245,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK2))
    | ~ spl21_2 ),
    inference(superposition,[],[f1421,f910])).

fof(f1421,plain,
    ( ! [X22] : r1_tarski(k4_xboole_0(X22,k4_xboole_0(sK0,sK1)),k4_xboole_0(X22,k4_xboole_0(sK0,sK2)))
    | ~ spl21_2 ),
    inference(resolution,[],[f1386,f754])).

fof(f754,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f530])).

fof(f530,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f94])).

fof(f94,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f1386,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl21_2 ),
    inference(forward_demodulation,[],[f1385,f1071])).

fof(f1385,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl21_2 ),
    inference(forward_demodulation,[],[f1012,f1028])).

fof(f1012,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl21_2 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1011,plain,
    ( spl21_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_2])])).

fof(f1373,plain,
    ( ~ spl21_1
    | spl21_2 ),
    inference(avatar_contradiction_clause,[],[f1372])).

fof(f1372,plain,
    ( $false
    | ~ spl21_1
    | spl21_2 ),
    inference(subsumption_resolution,[],[f1345,f1008])).

fof(f1008,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl21_1 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1345,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl21_2 ),
    inference(resolution,[],[f1171,f754])).

fof(f1171,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl21_2 ),
    inference(forward_demodulation,[],[f1066,f1071])).

fof(f1066,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl21_2 ),
    inference(forward_demodulation,[],[f1013,f1028])).

fof(f1013,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl21_2 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1015,plain,
    ( spl21_1
    | spl21_2 ),
    inference(avatar_split_clause,[],[f697,f1011,f1007])).

fof(f697,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f603])).

fof(f1014,plain,
    ( ~ spl21_1
    | ~ spl21_2 ),
    inference(avatar_split_clause,[],[f698,f1011,f1007])).

fof(f698,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f603])).
%------------------------------------------------------------------------------
