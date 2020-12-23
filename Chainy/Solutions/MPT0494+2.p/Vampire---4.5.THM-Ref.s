%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0494+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  63 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 175 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1092,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f860,f864,f868,f1071,f1086])).

fof(f1086,plain,
    ( ~ spl9_12
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f1085,f866,f862,f858,f1061])).

fof(f1061,plain,
    ( spl9_12
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f858,plain,
    ( spl9_1
  <=> r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f862,plain,
    ( spl9_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f866,plain,
    ( spl9_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1085,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f1084,f867])).

fof(f867,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f866])).

fof(f1084,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f1083,f863])).

fof(f863,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f862])).

fof(f1083,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f1072,f902])).

fof(f902,plain,
    ( ! [X9] : r1_tarski(k7_relat_1(sK1,X9),sK1)
    | ~ spl9_3 ),
    inference(resolution,[],[f838,f867])).

fof(f838,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f774])).

fof(f774,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f732])).

fof(f732,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1072,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl9_1 ),
    inference(resolution,[],[f819,f859])).

fof(f859,plain,
    ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f858])).

fof(f819,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f755])).

fof(f755,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f754])).

fof(f754,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f703])).

fof(f703,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

fof(f1071,plain,
    ( ~ spl9_3
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f1070])).

fof(f1070,plain,
    ( $false
    | ~ spl9_3
    | spl9_12 ),
    inference(subsumption_resolution,[],[f1068,f867])).

fof(f1068,plain,
    ( ~ v1_relat_1(sK1)
    | spl9_12 ),
    inference(resolution,[],[f1062,f839])).

fof(f839,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f775])).

fof(f775,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1062,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f868,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f799,f866])).

fof(f799,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f783])).

fof(f783,plain,
    ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f740,f782,f781])).

fof(f781,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f782,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),X2),k5_relat_1(sK1,X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f740,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f737])).

fof(f737,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f736])).

fof(f736,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(k7_relat_1(X1,X0),X2),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_relat_1)).

fof(f864,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f800,f862])).

fof(f800,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f783])).

fof(f860,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f801,f858])).

fof(f801,plain,(
    ~ r1_tarski(k5_relat_1(k7_relat_1(sK1,sK0),sK2),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f783])).
%------------------------------------------------------------------------------
