%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 132 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  295 ( 385 expanded)
%              Number of equality atoms :   41 (  59 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f113,f140,f297])).

fof(f297,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f295,f112])).

fof(f112,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f295,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f294,f93])).

fof(f93,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f294,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f290,f88])).

fof(f88,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f290,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f287,f83])).

fof(f83,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_1
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( v5_funct_1(X0,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f286,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) )
    | ~ spl5_7 ),
    inference(superposition,[],[f139,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f139,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f286,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f285,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f285,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f149,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f149,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(k1_relat_1(X6))
      | v5_funct_1(X6,X7)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f135,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f129,f56])).

fof(f129,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(superposition,[],[f77,f126])).

fof(f126,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f125,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f125,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f69,f75])).

fof(f75,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f77,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f140,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f134,f137])).

fof(f134,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f129,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK2(X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK3(X4),sK4(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK3(X4),sK4(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f113,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f108,f96,f110])).

fof(f96,plain,
    ( spl5_4
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f108,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f106,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f106,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | ~ spl5_4 ),
    inference(resolution,[],[f68,f98])).

fof(f98,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f99,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f76,f96])).

fof(f76,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f94,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f89,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f51,f86])).

fof(f51,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f52,f81])).

fof(f52,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:52:35 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.49  % (3312)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.50  % (3312)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (3320)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (3320)Refutation not found, incomplete strategy% (3320)------------------------------
% 0.22/0.50  % (3320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3320)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3320)Memory used [KB]: 1663
% 0.22/0.50  % (3320)Time elapsed: 0.003 s
% 0.22/0.50  % (3320)------------------------------
% 0.22/0.50  % (3320)------------------------------
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f113,f140,f297])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f296])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f295,f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0) | ~spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl5_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    ~v1_xboole_0(k1_xboole_0) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f294,f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    v1_relat_1(sK0) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl5_3 <=> v1_relat_1(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    ~v1_relat_1(sK0) | ~v1_xboole_0(k1_xboole_0) | (spl5_1 | ~spl5_2 | ~spl5_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f290,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    v1_funct_1(sK0) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl5_2 <=> v1_funct_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_xboole_0(k1_xboole_0) | (spl5_1 | ~spl5_7)),
% 0.22/0.51    inference(resolution,[],[f287,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ~v5_funct_1(k1_xboole_0,sK0) | spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl5_1 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v5_funct_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_xboole_0(X0)) ) | ~spl5_7),
% 0.22/0.51    inference(subsumption_resolution,[],[f286,f141])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) ) | ~spl5_7),
% 0.22/0.51    inference(superposition,[],[f139,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    v1_relat_1(k1_xboole_0) | ~spl5_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f137])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    spl5_7 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v5_funct_1(X0,X1) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f285,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v5_funct_1(X0,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(resolution,[],[f149,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~v1_xboole_0(k1_relat_1(X6)) | v5_funct_1(X6,X7) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.22/0.51    inference(resolution,[],[f135,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(rectify,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(superposition,[],[f129,f56])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.22/0.51    inference(superposition,[],[f77,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f125,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(superposition,[],[f69,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.51    inference(rectify,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.51    inference(equality_resolution,[],[f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.51    inference(flattening,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.51    inference(nnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    spl5_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f134,f137])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    v1_relat_1(k1_xboole_0)),
% 0.22/0.51    inference(resolution,[],[f129,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0))) & (! [X4] : (k4_tarski(sK3(X4),sK4(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f44,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK3(X4),sK4(X4)) = X4)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(rectify,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl5_5 | ~spl5_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f108,f96,f110])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    spl5_4 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0) | ~spl5_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f106,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~r1_tarski(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) | ~spl5_4),
% 0.22/0.51    inference(resolution,[],[f68,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f96])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl5_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f76,f96])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    inference(equality_resolution,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f50,f91])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v1_relat_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.51    inference(negated_conjecture,[],[f21])).
% 0.22/0.51  fof(f21,conjecture,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f51,f86])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v1_funct_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ~spl5_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f81])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (3312)------------------------------
% 0.22/0.51  % (3312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3312)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (3312)Memory used [KB]: 6396
% 0.22/0.51  % (3312)Time elapsed: 0.074 s
% 0.22/0.51  % (3312)------------------------------
% 0.22/0.51  % (3312)------------------------------
% 0.22/0.51  % (3290)Success in time 0.142 s
%------------------------------------------------------------------------------
