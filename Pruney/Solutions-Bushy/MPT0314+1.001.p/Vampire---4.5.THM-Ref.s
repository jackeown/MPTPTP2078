%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0314+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 139 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  199 ( 627 expanded)
%              Number of equality atoms :   65 ( 132 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2732,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f55,f75,f2674])).

fof(f2674,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f2673])).

fof(f2673,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f72,f2672])).

fof(f2672,plain,
    ( ! [X30,X28,X31,X29] : k2_xboole_0(k2_zfmisc_1(X28,k4_xboole_0(X29,X30)),k2_zfmisc_1(k4_xboole_0(X28,X31),X29)) = k4_xboole_0(k2_zfmisc_1(X28,X29),k2_zfmisc_1(X31,X30))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f2519,f1079])).

fof(f1079,plain,
    ( ! [X6,X4,X7,X5] : k4_xboole_0(k2_zfmisc_1(X6,X7),k2_zfmisc_1(X4,X5)) = k4_xboole_0(k2_zfmisc_1(X6,X7),k3_xboole_0(k2_zfmisc_1(X6,X5),k2_zfmisc_1(X4,X7)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f814,f168])).

fof(f168,plain,(
    ! [X6,X4,X7,X5] : k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)) = k3_xboole_0(k2_zfmisc_1(X5,X6),k2_zfmisc_1(X4,X7)) ),
    inference(superposition,[],[f132,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f132,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X1,X0),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f39,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f814,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f813,f67])).

fof(f67,plain,
    ( ! [X0] : k2_xboole_0(o_0_0_xboole_0,X0) = X0
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f57,f54])).

fof(f54,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_3
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f27,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f813,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X3,X2)) = k2_xboole_0(o_0_0_xboole_0,k4_xboole_0(X2,X3))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f786,f27])).

fof(f786,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),o_0_0_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f30,f780])).

fof(f780,plain,
    ( ! [X3] : o_0_0_xboole_0 = k4_xboole_0(X3,X3)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f772,f776])).

fof(f776,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(X0,X0,o_0_0_xboole_0),X1)
        | o_0_0_xboole_0 = k4_xboole_0(X0,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f772,f576])).

fof(f576,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,o_0_0_xboole_0)
        | ~ r2_hidden(X5,X4) )
    | ~ spl5_2 ),
    inference(superposition,[],[f41,f571])).

fof(f571,plain,
    ( ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0)
    | ~ spl5_2 ),
    inference(resolution,[],[f563,f49])).

fof(f49,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f563,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X3)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f561,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f561,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f772,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(X3,X3,o_0_0_xboole_0),o_0_0_xboole_0)
        | o_0_0_xboole_0 = k4_xboole_0(X3,X3) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f771])).

fof(f771,plain,
    ( ! [X3] :
        ( o_0_0_xboole_0 = k4_xboole_0(X3,X3)
        | r2_hidden(sK4(X3,X3,o_0_0_xboole_0),o_0_0_xboole_0)
        | o_0_0_xboole_0 = k4_xboole_0(X3,X3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f37,f640])).

fof(f640,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,o_0_0_xboole_0),X0)
        | k4_xboole_0(X0,X1) = o_0_0_xboole_0 )
    | ~ spl5_2 ),
    inference(resolution,[],[f553,f49])).

fof(f553,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_xboole_0(X6)
      | k4_xboole_0(X4,X5) = X6
      | r2_hidden(sK4(X4,X5,X6),X4) ) ),
    inference(resolution,[],[f36,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f2519,plain,(
    ! [X30,X28,X31,X29] : k4_xboole_0(k2_zfmisc_1(X28,X29),k3_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X31,X29))) = k2_xboole_0(k2_zfmisc_1(X28,k4_xboole_0(X29,X30)),k2_zfmisc_1(k4_xboole_0(X28,X31),X29)) ),
    inference(superposition,[],[f86,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(X3,k2_zfmisc_1(X2,X1))) = k2_xboole_0(k4_xboole_0(k2_zfmisc_1(X0,X1),X3),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) ),
    inference(superposition,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_4
  <=> k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f75,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f66,f44,f71])).

fof(f44,plain,
    ( spl5_1
  <=> k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f66,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1))
    | spl5_1 ),
    inference(superposition,[],[f45,f27])).

fof(f45,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f55,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f51,f48,f53])).

fof(f51,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_2 ),
    inference(resolution,[],[f26,f49])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f50,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f46,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))
   => k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) != k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

%------------------------------------------------------------------------------
