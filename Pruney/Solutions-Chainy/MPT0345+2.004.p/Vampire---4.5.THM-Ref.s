%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 340 expanded)
%              Number of leaves         :   15 ( 115 expanded)
%              Depth                    :   21
%              Number of atoms          :  401 (2529 expanded)
%              Number of equality atoms :   31 ( 255 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f557,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f231,f394,f432,f437,f472,f513,f522,f556])).

fof(f556,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f226,f229,f388,f71])).

fof(f71,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != k4_subset_1(sK0,sK2,sK3)
    & ! [X4] :
        ( ( ( r2_hidden(X4,sK1)
            | ( ~ r2_hidden(X4,sK3)
              & ~ r2_hidden(X4,sK2) ) )
          & ( r2_hidden(X4,sK3)
            | r2_hidden(X4,sK2)
            | ~ r2_hidden(X4,sK1) ) )
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k4_subset_1(X0,X2,X3) != X1
                & ! [X4] :
                    ( ( ( r2_hidden(X4,X1)
                        | ( ~ r2_hidden(X4,X3)
                          & ~ r2_hidden(X4,X2) ) )
                      & ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2)
                        | ~ r2_hidden(X4,X1) ) )
                    | ~ m1_subset_1(X4,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != k4_subset_1(sK0,X2,X3)
              & ! [X4] :
                  ( ( ( r2_hidden(X4,sK1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,sK1) ) )
                  | ~ m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != k4_subset_1(sK0,X2,X3)
            & ! [X4] :
                ( ( ( r2_hidden(X4,sK1)
                    | ( ~ r2_hidden(X4,X3)
                      & ~ r2_hidden(X4,X2) ) )
                  & ( r2_hidden(X4,X3)
                    | r2_hidden(X4,X2)
                    | ~ r2_hidden(X4,sK1) ) )
                | ~ m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( sK1 != k4_subset_1(sK0,sK2,X3)
          & ! [X4] :
              ( ( ( r2_hidden(X4,sK1)
                  | ( ~ r2_hidden(X4,X3)
                    & ~ r2_hidden(X4,sK2) ) )
                & ( r2_hidden(X4,X3)
                  | r2_hidden(X4,sK2)
                  | ~ r2_hidden(X4,sK1) ) )
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( sK1 != k4_subset_1(sK0,sK2,X3)
        & ! [X4] :
            ( ( ( r2_hidden(X4,sK1)
                | ( ~ r2_hidden(X4,X3)
                  & ~ r2_hidden(X4,sK2) ) )
              & ( r2_hidden(X4,X3)
                | r2_hidden(X4,sK2)
                | ~ r2_hidden(X4,sK1) ) )
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( sK1 != k4_subset_1(sK0,sK2,sK3)
      & ! [X4] :
          ( ( ( r2_hidden(X4,sK1)
              | ( ~ r2_hidden(X4,sK3)
                & ~ r2_hidden(X4,sK2) ) )
            & ( r2_hidden(X4,sK3)
              | r2_hidden(X4,sK2)
              | ~ r2_hidden(X4,sK1) ) )
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( ( r2_hidden(X4,X1)
                      | ( ~ r2_hidden(X4,X3)
                        & ~ r2_hidden(X4,X2) ) )
                    & ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2)
                      | ~ r2_hidden(X4,X1) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k4_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( r2_hidden(X4,X3)
                      | r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( r2_hidden(X4,X3)
                          | r2_hidden(X4,X2) ) ) )
                 => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( r2_hidden(X4,X3)
                        | r2_hidden(X4,X2) ) ) )
               => k4_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_subset_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f35,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f388,plain,
    ( r2_hidden(sK4(sK2,sK3,sK1),sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl6_7
  <=> r2_hidden(sK4(sK2,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f229,plain,
    ( r2_hidden(sK4(sK2,sK3,sK1),sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl6_2
  <=> r2_hidden(sK4(sK2,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f226,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl6_1
  <=> r2_hidden(sK4(sK2,sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f522,plain,
    ( ~ spl6_2
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | ~ spl6_2
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f28,f389,f229,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f389,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f387])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f513,plain,
    ( spl6_7
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | spl6_7
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f29,f389,f392,f38])).

fof(f392,plain,
    ( r2_hidden(sK4(sK2,sK3,sK1),sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl6_8
  <=> r2_hidden(sK4(sK2,sK3,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f472,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f470,f388])).

fof(f470,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f469,f225])).

fof(f225,plain,
    ( r2_hidden(sK4(sK2,sK3,sK1),sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f224])).

fof(f469,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK1)
    | ~ r2_hidden(sK4(sK2,sK3,sK1),sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f460,f230])).

fof(f230,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f228])).

fof(f460,plain,
    ( r2_hidden(sK4(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK4(sK2,sK3,sK1),sK1)
    | ~ r2_hidden(sK4(sK2,sK3,sK1),sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f454,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK3)
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f68,f30])).

fof(f30,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | r2_hidden(X4,sK2)
      | ~ r2_hidden(X4,sK1)
      | r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f454,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f85,f225])).

fof(f85,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK4(sK2,sK3,sK1),sK1) ),
    inference(resolution,[],[f83,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f46,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f83,plain,(
    ~ sQ5_eqProxy(k2_xboole_0(sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f82,f28])).

fof(f82,plain,
    ( ~ sQ5_eqProxy(k2_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f78,f29])).

fof(f78,plain,
    ( ~ sQ5_eqProxy(k2_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f74,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_subset_1(X0,X1,X2),k2_xboole_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f40,f50])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f74,plain,(
    ! [X1] :
      ( ~ sQ5_eqProxy(k4_subset_1(sK0,sK2,sK3),X1)
      | ~ sQ5_eqProxy(X1,sK1) ) ),
    inference(resolution,[],[f65,f66])).

fof(f66,plain,(
    ~ sQ5_eqProxy(k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(resolution,[],[f64,f51])).

fof(f51,plain,(
    ~ sQ5_eqProxy(sK1,k4_subset_1(sK0,sK2,sK3)) ),
    inference(equality_proxy_replacement,[],[f33,f50])).

fof(f33,plain,(
    sK1 != k4_subset_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sQ5_eqProxy(X1,X0)
      | ~ sQ5_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f50])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(X0,X2)
      | ~ sQ5_eqProxy(X1,X2)
      | ~ sQ5_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f50])).

fof(f437,plain,
    ( ~ spl6_1
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl6_1
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f27,f389,f225,f38])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f432,plain,
    ( spl6_1
    | spl6_2
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f83,f230,f226,f393,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | sQ5_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f44,f50])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f393,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK3)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f391])).

fof(f394,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f236,f224,f391,f387])).

fof(f236,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK3)
    | ~ r2_hidden(sK4(sK2,sK3,sK1),sK0)
    | spl6_1 ),
    inference(resolution,[],[f226,f70])).

fof(f70,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f68,f32])).

fof(f32,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK3)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f231,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f84,f228,f224])).

fof(f84,plain,
    ( ~ r2_hidden(sK4(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK4(sK2,sK3,sK1),sK1) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f45,f50])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:13:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (7476)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (7492)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (7484)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (7477)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (7479)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (7494)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (7495)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (7477)Refutation not found, incomplete strategy% (7477)------------------------------
% 0.21/0.50  % (7477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7477)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7477)Memory used [KB]: 10746
% 0.21/0.50  % (7477)Time elapsed: 0.068 s
% 0.21/0.50  % (7477)------------------------------
% 0.21/0.50  % (7477)------------------------------
% 0.21/0.50  % (7481)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (7482)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (7488)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (7483)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (7486)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (7489)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (7480)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (7493)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (7491)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (7485)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (7487)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (7487)Refutation not found, incomplete strategy% (7487)------------------------------
% 0.21/0.52  % (7487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7487)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7487)Memory used [KB]: 10618
% 0.21/0.52  % (7487)Time elapsed: 0.105 s
% 0.21/0.52  % (7487)------------------------------
% 0.21/0.52  % (7487)------------------------------
% 0.21/0.52  % (7478)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (7490)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % (7496)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.55  % (7481)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f557,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f231,f394,f432,f437,f472,f513,f522,f556])).
% 0.21/0.55  fof(f556,plain,(
% 0.21/0.55    spl6_1 | ~spl6_2 | ~spl6_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f555])).
% 0.21/0.55  fof(f555,plain,(
% 0.21/0.55    $false | (spl6_1 | ~spl6_2 | ~spl6_7)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f226,f229,f388,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X2] : (r2_hidden(X2,sK1) | ~r2_hidden(X2,sK2) | ~r2_hidden(X2,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f68,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK2) | r2_hidden(X4,sK1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ((sK1 != k4_subset_1(sK0,sK2,sK3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,sK3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,sK3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f19,f18,f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (sK1 != k4_subset_1(sK0,X2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X2] : (? [X3] : (sK1 != k4_subset_1(sK0,X2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (sK1 != k4_subset_1(sK0,sK2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,X3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X3] : (sK1 != k4_subset_1(sK0,sK2,X3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,X3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (sK1 != k4_subset_1(sK0,sK2,sK3) & ! [X4] : (((r2_hidden(X4,sK1) | (~r2_hidden(X4,sK3) & ~r2_hidden(X4,sK2))) & (r2_hidden(X4,sK3) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1))) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & (r2_hidden(X4,X3) | r2_hidden(X4,X2) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : (((r2_hidden(X4,X1) | (~r2_hidden(X4,X3) & ~r2_hidden(X4,X2))) & ((r2_hidden(X4,X3) | r2_hidden(X4,X2)) | ~r2_hidden(X4,X1))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : (? [X3] : (k4_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f8])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : (? [X3] : ((k4_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 0.21/0.55    inference(negated_conjecture,[],[f6])).
% 0.21/0.55  fof(f6,conjecture,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (r2_hidden(X4,X3) | r2_hidden(X4,X2)))) => k4_subset_1(X0,X2,X3) = X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_subset_1)).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f35,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.55  fof(f388,plain,(
% 0.21/0.55    r2_hidden(sK4(sK2,sK3,sK1),sK0) | ~spl6_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f387])).
% 0.21/0.55  fof(f387,plain,(
% 0.21/0.55    spl6_7 <=> r2_hidden(sK4(sK2,sK3,sK1),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.55  fof(f229,plain,(
% 0.21/0.55    r2_hidden(sK4(sK2,sK3,sK1),sK2) | ~spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f228])).
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    spl6_2 <=> r2_hidden(sK4(sK2,sK3,sK1),sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK1) | spl6_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f224])).
% 0.21/0.55  fof(f224,plain,(
% 0.21/0.55    spl6_1 <=> r2_hidden(sK4(sK2,sK3,sK1),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.55  fof(f522,plain,(
% 0.21/0.55    ~spl6_2 | spl6_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f520])).
% 0.21/0.55  fof(f520,plain,(
% 0.21/0.55    $false | (~spl6_2 | spl6_7)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f28,f389,f229,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.55  fof(f389,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK0) | spl6_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f387])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f513,plain,(
% 0.21/0.55    spl6_7 | ~spl6_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f512])).
% 0.21/0.55  fof(f512,plain,(
% 0.21/0.55    $false | (spl6_7 | ~spl6_8)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f29,f389,f392,f38])).
% 0.21/0.55  fof(f392,plain,(
% 0.21/0.55    r2_hidden(sK4(sK2,sK3,sK1),sK3) | ~spl6_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f391])).
% 0.21/0.55  fof(f391,plain,(
% 0.21/0.55    spl6_8 <=> r2_hidden(sK4(sK2,sK3,sK1),sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f472,plain,(
% 0.21/0.55    ~spl6_1 | spl6_2 | ~spl6_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f471])).
% 0.21/0.55  fof(f471,plain,(
% 0.21/0.55    $false | (~spl6_1 | spl6_2 | ~spl6_7)),
% 0.21/0.55    inference(subsumption_resolution,[],[f470,f388])).
% 0.21/0.55  fof(f470,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK0) | (~spl6_1 | spl6_2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f469,f225])).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    r2_hidden(sK4(sK2,sK3,sK1),sK1) | ~spl6_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f224])).
% 0.21/0.55  fof(f469,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK1) | ~r2_hidden(sK4(sK2,sK3,sK1),sK0) | (~spl6_1 | spl6_2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f460,f230])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK2) | spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f228])).
% 0.21/0.55  fof(f460,plain,(
% 0.21/0.55    r2_hidden(sK4(sK2,sK3,sK1),sK2) | ~r2_hidden(sK4(sK2,sK3,sK1),sK1) | ~r2_hidden(sK4(sK2,sK3,sK1),sK0) | ~spl6_1),
% 0.21/0.55    inference(resolution,[],[f454,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,sK3) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f68,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X4] : (~m1_subset_1(X4,sK0) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1) | r2_hidden(X4,sK3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f454,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK3) | ~spl6_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f85,f225])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK3) | ~r2_hidden(sK4(sK2,sK3,sK1),sK1)),
% 0.21/0.55    inference(resolution,[],[f83,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f46,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.55    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k2_xboole_0(sK2,sK3),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f82,f28])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k2_xboole_0(sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f78,f29])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k2_xboole_0(sK2,sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(resolution,[],[f74,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sQ5_eqProxy(k4_subset_1(X0,X1,X2),k2_xboole_0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f40,f50])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(flattening,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X1] : (~sQ5_eqProxy(k4_subset_1(sK0,sK2,sK3),X1) | ~sQ5_eqProxy(X1,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f65,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ~sQ5_eqProxy(k4_subset_1(sK0,sK2,sK3),sK1)),
% 0.21/0.55    inference(resolution,[],[f64,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ~sQ5_eqProxy(sK1,k4_subset_1(sK0,sK2,sK3))),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f33,f50])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    sK1 != k4_subset_1(sK0,sK2,sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sQ5_eqProxy(X1,X0) | ~sQ5_eqProxy(X0,X1)) )),
% 0.21/0.55    inference(equality_proxy_axiom,[],[f50])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sQ5_eqProxy(X0,X2) | ~sQ5_eqProxy(X1,X2) | ~sQ5_eqProxy(X0,X1)) )),
% 0.21/0.55    inference(equality_proxy_axiom,[],[f50])).
% 0.21/0.55  fof(f437,plain,(
% 0.21/0.55    ~spl6_1 | spl6_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f435])).
% 0.21/0.55  fof(f435,plain,(
% 0.21/0.55    $false | (~spl6_1 | spl6_7)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f27,f389,f225,f38])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f432,plain,(
% 0.21/0.55    spl6_1 | spl6_2 | spl6_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f424])).
% 0.21/0.55  fof(f424,plain,(
% 0.21/0.55    $false | (spl6_1 | spl6_2 | spl6_8)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f83,f230,f226,f393,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | sQ5_eqProxy(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f44,f50])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f393,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK3) | spl6_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f391])).
% 0.21/0.55  fof(f394,plain,(
% 0.21/0.55    ~spl6_7 | ~spl6_8 | spl6_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f236,f224,f391,f387])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK3) | ~r2_hidden(sK4(sK2,sK3,sK1),sK0) | spl6_1),
% 0.21/0.55    inference(resolution,[],[f226,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK3) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f68,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK3) | r2_hidden(X4,sK1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    ~spl6_1 | ~spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f84,f228,f224])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ~r2_hidden(sK4(sK2,sK3,sK1),sK2) | ~r2_hidden(sK4(sK2,sK3,sK1),sK1)),
% 0.21/0.55    inference(resolution,[],[f83,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f45,f50])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (7481)------------------------------
% 0.21/0.55  % (7481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7481)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (7481)Memory used [KB]: 6396
% 0.21/0.55  % (7481)Time elapsed: 0.123 s
% 0.21/0.55  % (7481)------------------------------
% 0.21/0.55  % (7481)------------------------------
% 0.21/0.55  % (7475)Success in time 0.183 s
%------------------------------------------------------------------------------
