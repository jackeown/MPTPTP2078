%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0716+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 9.29s
% Output     : Refutation 9.29s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 160 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 ( 680 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2685,f2690,f2691,f2793,f4037,f5180])).

fof(f5180,plain,
    ( ~ spl129_1
    | spl129_2 ),
    inference(avatar_contradiction_clause,[],[f5179])).

fof(f5179,plain,
    ( $false
    | ~ spl129_1
    | spl129_2 ),
    inference(subsumption_resolution,[],[f5178,f1640])).

fof(f1640,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1049])).

fof(f1049,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1048])).

fof(f1048,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f986])).

fof(f986,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f985])).

fof(f985,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f5178,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl129_1
    | spl129_2 ),
    inference(subsumption_resolution,[],[f5177,f1641])).

fof(f1641,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1049])).

fof(f5177,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl129_1
    | spl129_2 ),
    inference(subsumption_resolution,[],[f5166,f2813])).

fof(f2813,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl129_1 ),
    inference(subsumption_resolution,[],[f2812,f1640])).

fof(f2812,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl129_1 ),
    inference(subsumption_resolution,[],[f2798,f1638])).

fof(f1638,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1049])).

fof(f2798,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl129_1 ),
    inference(superposition,[],[f2680,f1794])).

fof(f1794,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1195])).

fof(f1195,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f784])).

fof(f784,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f2680,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl129_1 ),
    inference(avatar_component_clause,[],[f2678])).

fof(f2678,plain,
    ( spl129_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl129_1])])).

fof(f5166,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl129_2 ),
    inference(resolution,[],[f4107,f1658])).

fof(f1658,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1072])).

fof(f1072,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1071])).

fof(f1071,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f956])).

fof(f956,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f4107,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k9_relat_1(sK0,X3),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,X3) )
    | spl129_2 ),
    inference(subsumption_resolution,[],[f4082,f1640])).

fof(f4082,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k9_relat_1(sK0,X3),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,X3)
        | ~ v1_relat_1(sK0) )
    | spl129_2 ),
    inference(resolution,[],[f4064,f1651])).

fof(f1651,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1062])).

fof(f1062,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1061])).

fof(f1061,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f759])).

fof(f759,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f4064,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | spl129_2 ),
    inference(resolution,[],[f2683,f1691])).

fof(f1691,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1099])).

fof(f1099,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1098])).

fof(f1098,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2683,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | spl129_2 ),
    inference(avatar_component_clause,[],[f2682])).

fof(f2682,plain,
    ( spl129_2
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl129_2])])).

fof(f4037,plain,
    ( ~ spl129_1
    | spl129_3 ),
    inference(avatar_contradiction_clause,[],[f4025])).

fof(f4025,plain,
    ( $false
    | ~ spl129_1
    | spl129_3 ),
    inference(resolution,[],[f3000,f2813])).

fof(f3000,plain,
    ( ! [X19] : ~ r1_tarski(sK2,k10_relat_1(sK0,X19))
    | spl129_3 ),
    inference(subsumption_resolution,[],[f2970,f1640])).

fof(f2970,plain,
    ( ! [X19] :
        ( ~ r1_tarski(sK2,k10_relat_1(sK0,X19))
        | ~ v1_relat_1(sK0) )
    | spl129_3 ),
    inference(resolution,[],[f2794,f1773])).

fof(f1773,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1181])).

fof(f1181,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f769])).

fof(f769,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f2794,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,X0) )
    | spl129_3 ),
    inference(resolution,[],[f2688,f1691])).

fof(f2688,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl129_3 ),
    inference(avatar_component_clause,[],[f2687])).

fof(f2687,plain,
    ( spl129_3
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl129_3])])).

fof(f2793,plain,
    ( spl129_1
    | ~ spl129_2
    | ~ spl129_3 ),
    inference(avatar_contradiction_clause,[],[f2792])).

fof(f2792,plain,
    ( $false
    | spl129_1
    | ~ spl129_2
    | ~ spl129_3 ),
    inference(subsumption_resolution,[],[f2791,f1640])).

fof(f2791,plain,
    ( ~ v1_relat_1(sK0)
    | spl129_1
    | ~ spl129_2
    | ~ spl129_3 ),
    inference(subsumption_resolution,[],[f2790,f2684])).

fof(f2684,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl129_2 ),
    inference(avatar_component_clause,[],[f2682])).

fof(f2790,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | spl129_1
    | ~ spl129_3 ),
    inference(subsumption_resolution,[],[f2789,f2689])).

fof(f2689,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl129_3 ),
    inference(avatar_component_clause,[],[f2687])).

fof(f2789,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | spl129_1 ),
    inference(subsumption_resolution,[],[f2785,f1641])).

fof(f2785,plain,
    ( ~ v1_funct_1(sK0)
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | spl129_1 ),
    inference(resolution,[],[f2721,f1642])).

fof(f1642,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1051])).

fof(f1051,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1050])).

fof(f1050,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f976])).

fof(f976,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f2721,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | spl129_1 ),
    inference(subsumption_resolution,[],[f2720,f1640])).

fof(f2720,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | spl129_1 ),
    inference(subsumption_resolution,[],[f2715,f1638])).

fof(f2715,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl129_1 ),
    inference(superposition,[],[f2679,f1794])).

fof(f2679,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl129_1 ),
    inference(avatar_component_clause,[],[f2678])).

fof(f2691,plain,
    ( ~ spl129_1
    | ~ spl129_2
    | ~ spl129_3 ),
    inference(avatar_split_clause,[],[f1635,f2687,f2682,f2678])).

fof(f1635,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1049])).

fof(f2690,plain,
    ( spl129_1
    | spl129_3 ),
    inference(avatar_split_clause,[],[f1636,f2687,f2678])).

fof(f1636,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1049])).

fof(f2685,plain,
    ( spl129_1
    | spl129_2 ),
    inference(avatar_split_clause,[],[f1637,f2682,f2678])).

fof(f1637,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1049])).
%------------------------------------------------------------------------------
