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
% DateTime   : Thu Dec  3 12:52:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 209 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   20
%              Number of atoms          :  259 ( 981 expanded)
%              Number of equality atoms :   27 ( 147 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f65,f71,f94])).

fof(f94,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f92,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0))
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0))
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(X1))
             => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f91,f77])).

fof(f77,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f76,f17])).

fof(f76,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f75,f19])).

fof(f19,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f74,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f73,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f72,f18])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f43,plain,(
    ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f42,f17])).

fof(f42,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f41,f22])).

fof(f41,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f40,f21])).

fof(f40,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f39,f18])).

fof(f39,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f20,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f20,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f91,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f85,f18])).

fof(f85,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(superposition,[],[f56,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f56,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_3
  <=> k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f71,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f69,f21])).

fof(f69,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f68,f18])).

fof(f68,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f67,f17])).

fof(f67,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f66,f22])).

fof(f66,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(resolution,[],[f52,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f52,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_2
  <=> v1_funct_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f63,f21])).

fof(f63,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f62,f18])).

fof(f62,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f61,f17])).

fof(f61,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f60,f22])).

fof(f60,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(resolution,[],[f48,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_1
  <=> v1_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f58,f54,f50,f46])).

fof(f58,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f38,f43])).

fof(f38,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(superposition,[],[f20,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:40:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.48  % (10272)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (10259)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (10264)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (10262)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (10259)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f59,f65,f71,f94])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    $false | spl3_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) != k1_funct_1(X2,k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f76,f17])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ~r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f74,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    v1_funct_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f73,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f72,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(resolution,[],[f43,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f42,f17])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f41,f22])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f40,f21])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f39,f18])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) | ~v1_relat_1(sK2)),
% 0.22/0.49    inference(superposition,[],[f20,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f85,f18])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    k1_xboole_0 != k1_xboole_0 | ~v1_funct_1(sK2) | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.49    inference(superposition,[],[f56,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_funct_1(X0,X1) = k1_xboole_0 | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl3_3 <=> k1_xboole_0 = k1_funct_1(sK2,k1_funct_1(sK1,sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    $false | spl3_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f21])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl3_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f18])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | spl3_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f67,f17])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | spl3_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f22])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | spl3_2),
% 0.22/0.49    inference(resolution,[],[f52,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ~v1_funct_1(k5_relat_1(sK1,sK2)) | spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl3_2 <=> v1_funct_1(k5_relat_1(sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    $false | spl3_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f63,f21])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl3_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f62,f18])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | spl3_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f61,f17])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | spl3_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f60,f22])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | spl3_1),
% 0.22/0.49    inference(resolution,[],[f48,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ~v1_relat_1(k5_relat_1(sK1,sK2)) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl3_1 <=> v1_relat_1(k5_relat_1(sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f58,f54,f50,f46])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | ~v1_funct_1(k5_relat_1(sK1,sK2)) | ~v1_relat_1(k5_relat_1(sK1,sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f38,f43])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    k1_xboole_0 != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) | ~v1_funct_1(k5_relat_1(sK1,sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) | ~v1_relat_1(k5_relat_1(sK1,sK2))),
% 0.22/0.49    inference(superposition,[],[f20,f34])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10259)------------------------------
% 0.22/0.49  % (10259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10259)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10259)Memory used [KB]: 10618
% 0.22/0.49  % (10259)Time elapsed: 0.062 s
% 0.22/0.49  % (10259)------------------------------
% 0.22/0.49  % (10259)------------------------------
% 0.22/0.50  % (10255)Success in time 0.127 s
%------------------------------------------------------------------------------
