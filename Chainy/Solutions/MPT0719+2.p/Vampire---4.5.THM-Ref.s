%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0719+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:46 EST 2020

% Result     : Theorem 4.69s
% Output     : Refutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   59 (  84 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  180 ( 248 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2452,f2457,f2462,f2554,f6805,f7603,f8074,f8592])).

fof(f8592,plain,
    ( ~ spl123_1
    | ~ spl123_2
    | spl123_3
    | ~ spl123_19
    | ~ spl123_31
    | ~ spl123_34
    | ~ spl123_38 ),
    inference(avatar_contradiction_clause,[],[f8591])).

fof(f8591,plain,
    ( $false
    | ~ spl123_1
    | ~ spl123_2
    | spl123_3
    | ~ spl123_19
    | ~ spl123_31
    | ~ spl123_34
    | ~ spl123_38 ),
    inference(subsumption_resolution,[],[f8590,f7669])).

fof(f7669,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl123_19 ),
    inference(unit_resulting_resolution,[],[f2553,f2274])).

fof(f2274,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1411])).

fof(f1411,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f2553,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl123_19 ),
    inference(avatar_component_clause,[],[f2551])).

fof(f2551,plain,
    ( spl123_19
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl123_19])])).

fof(f8590,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl123_1
    | ~ spl123_2
    | spl123_3
    | ~ spl123_31
    | ~ spl123_34
    | ~ spl123_38 ),
    inference(forward_demodulation,[],[f8582,f6804])).

fof(f6804,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl123_31 ),
    inference(avatar_component_clause,[],[f6802])).

fof(f6802,plain,
    ( spl123_31
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl123_31])])).

fof(f8582,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl123_1
    | ~ spl123_2
    | spl123_3
    | ~ spl123_34
    | ~ spl123_38 ),
    inference(unit_resulting_resolution,[],[f2451,f2456,f7602,f2461,f8073,f1707])).

fof(f1707,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1440])).

fof(f1440,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f1438,f1439])).

fof(f1439,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1438,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1437])).

fof(f1437,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1058])).

fof(f1058,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1057])).

fof(f1057,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f901])).

fof(f901,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f8073,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl123_38 ),
    inference(avatar_component_clause,[],[f8071])).

fof(f8071,plain,
    ( spl123_38
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl123_38])])).

fof(f2461,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl123_3 ),
    inference(avatar_component_clause,[],[f2459])).

fof(f2459,plain,
    ( spl123_3
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl123_3])])).

fof(f7602,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl123_34 ),
    inference(avatar_component_clause,[],[f7600])).

fof(f7600,plain,
    ( spl123_34
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl123_34])])).

fof(f2456,plain,
    ( v1_funct_1(sK0)
    | ~ spl123_2 ),
    inference(avatar_component_clause,[],[f2454])).

fof(f2454,plain,
    ( spl123_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl123_2])])).

fof(f2451,plain,
    ( v1_relat_1(sK0)
    | ~ spl123_1 ),
    inference(avatar_component_clause,[],[f2449])).

fof(f2449,plain,
    ( spl123_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl123_1])])).

fof(f8074,plain,
    ( spl123_38
    | ~ spl123_19 ),
    inference(avatar_split_clause,[],[f6816,f2551,f8071])).

fof(f6816,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl123_19 ),
    inference(unit_resulting_resolution,[],[f2553,f2300])).

fof(f2300,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f1432])).

fof(f1432,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f889])).

fof(f889,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f7603,plain,
    ( spl123_34
    | ~ spl123_19 ),
    inference(avatar_split_clause,[],[f6813,f2551,f7600])).

fof(f6813,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl123_19 ),
    inference(unit_resulting_resolution,[],[f2553,f2299])).

fof(f2299,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1431])).

fof(f1431,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f6805,plain,(
    spl123_31 ),
    inference(avatar_split_clause,[],[f2075,f6802])).

fof(f2075,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f2554,plain,(
    spl123_19 ),
    inference(avatar_split_clause,[],[f2305,f2551])).

fof(f2305,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f2462,plain,(
    ~ spl123_3 ),
    inference(avatar_split_clause,[],[f1705,f2459])).

fof(f1705,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f1436])).

fof(f1436,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1056,f1435])).

fof(f1435,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1056,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1055])).

fof(f1055,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f996])).

fof(f996,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f995])).

fof(f995,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f2457,plain,(
    spl123_2 ),
    inference(avatar_split_clause,[],[f1704,f2454])).

fof(f1704,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1436])).

fof(f2452,plain,(
    spl123_1 ),
    inference(avatar_split_clause,[],[f1703,f2449])).

fof(f1703,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1436])).
%------------------------------------------------------------------------------
