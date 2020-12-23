%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 312 expanded)
%              Number of leaves         :   19 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  364 (1534 expanded)
%              Number of equality atoms :   88 ( 358 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f579,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f50,f80,f84,f121,f133,f141,f147,f377,f395,f413,f538,f573])).

fof(f573,plain,
    ( spl5_1
    | ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | spl5_1
    | ~ spl5_30 ),
    inference(trivial_inequality_removal,[],[f562])).

fof(f562,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK0,sK2)
    | spl5_1
    | ~ spl5_30 ),
    inference(superposition,[],[f42,f540])).

fof(f540,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl5_30 ),
    inference(trivial_inequality_removal,[],[f539])).

fof(f539,plain,
    ( sK2 != sK2
    | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl5_30 ),
    inference(superposition,[],[f224,f56])).

fof(f56,plain,(
    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(global_subsumption,[],[f26,f54])).

fof(f54,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <~> ! [X3] :
                    ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                    | ~ r2_hidden(X3,X2) ) )
              & r1_tarski(X2,k1_relat_1(X1))
              & r1_tarski(X2,k1_relat_1(X0)) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( r1_tarski(X2,k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
               => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
                <=> ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X1,X3) = k1_funct_1(X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( r1_tarski(X2,k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) )
             => ( k7_relat_1(X0,X2) = k7_relat_1(X1,X2)
              <=> ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X1,X3) = k1_funct_1(X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f224,plain,
    ( ! [X1] :
        ( sK2 != k1_relat_1(k7_relat_1(sK0,X1))
        | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X1) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl5_30
  <=> ! [X1] :
        ( sK2 != k1_relat_1(k7_relat_1(sK0,X1))
        | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f42,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl5_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f538,plain,
    ( ~ spl5_12
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_11
    | spl5_30
    | ~ spl5_2
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f537,f220,f39,f223,f97,f70,f73,f100])).

fof(f100,plain,
    ( spl5_12
  <=> v1_relat_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f73,plain,
    ( spl5_8
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f70,plain,
    ( spl5_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f97,plain,
    ( spl5_11
  <=> v1_funct_1(k7_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f39,plain,
    ( spl5_2
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | k1_funct_1(sK1,X3) = k1_funct_1(sK0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f220,plain,
    ( spl5_29
  <=> r2_hidden(sK4(k7_relat_1(sK1,sK2),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f537,plain,
    ( ! [X0] :
        ( sK2 != k1_relat_1(k7_relat_1(sK0,X0))
        | ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK2))
        | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X0) )
    | ~ spl5_2
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f536,f52])).

fof(f52,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK0,X1)) = k3_xboole_0(k1_relat_1(sK0),X1) ),
    inference(resolution,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f536,plain,
    ( ! [X0] :
        ( sK2 != k3_xboole_0(k1_relat_1(sK0),X0)
        | ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK2))
        | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X0) )
    | ~ spl5_2
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f535,f57])).

fof(f57,plain,(
    sK2 = k1_relat_1(k7_relat_1(sK1,sK2)) ),
    inference(global_subsumption,[],[f24,f55])).

fof(f55,plain,
    ( ~ v1_relat_1(sK1)
    | sK2 = k1_relat_1(k7_relat_1(sK1,sK2)) ),
    inference(resolution,[],[f29,f23])).

fof(f23,plain,(
    r1_tarski(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f535,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK0)
        | k3_xboole_0(k1_relat_1(sK0),X0) != k1_relat_1(k7_relat_1(sK1,sK2))
        | ~ v1_relat_1(k7_relat_1(sK1,sK2))
        | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X0) )
    | ~ spl5_2
    | ~ spl5_29 ),
    inference(trivial_inequality_removal,[],[f534])).

fof(f534,plain,
    ( ! [X0] :
        ( k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),sK0))
        | ~ v1_funct_1(k7_relat_1(sK1,sK2))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK0)
        | k3_xboole_0(k1_relat_1(sK0),X0) != k1_relat_1(k7_relat_1(sK1,sK2))
        | ~ v1_relat_1(k7_relat_1(sK1,sK2))
        | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X0) )
    | ~ spl5_2
    | ~ spl5_29 ),
    inference(superposition,[],[f33,f523])).

fof(f523,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),sK0))
    | ~ spl5_2
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f241,f423])).

fof(f423,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),sK0))
    | ~ spl5_2
    | ~ spl5_29 ),
    inference(resolution,[],[f221,f40])).

fof(f40,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | k1_funct_1(sK1,X3) = k1_funct_1(sK0,X3) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f221,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,sK2),sK0),sK2)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f220])).

fof(f241,plain,
    ( k1_funct_1(sK1,sK4(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK1,sK2),sK0))
    | ~ spl5_29 ),
    inference(resolution,[],[f221,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK1,X0) = k1_funct_1(k7_relat_1(sK1,sK2),X0) ) ),
    inference(global_subsumption,[],[f24,f25,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = k1_funct_1(k7_relat_1(sK1,sK2),X0) ) ),
    inference(superposition,[],[f34,f57])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f25,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,sK4(X1,X2)) != k1_funct_1(X2,sK4(X1,X2))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X2,X0) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ? [X3] :
              ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
              & r2_hidden(X3,k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
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
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(f413,plain,
    ( spl5_29
    | ~ spl5_12
    | ~ spl5_11
    | spl5_30 ),
    inference(avatar_split_clause,[],[f405,f223,f97,f100,f220])).

fof(f405,plain,(
    ! [X11] :
      ( sK2 != k1_relat_1(k7_relat_1(sK0,X11))
      | ~ v1_funct_1(k7_relat_1(sK1,sK2))
      | ~ v1_relat_1(k7_relat_1(sK1,sK2))
      | r2_hidden(sK4(k7_relat_1(sK1,sK2),sK0),sK2)
      | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X11) ) ),
    inference(superposition,[],[f113,f57])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k7_relat_1(sK0,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,sK0),k1_relat_1(X1))
      | k7_relat_1(sK0,X0) = X1 ) ),
    inference(global_subsumption,[],[f26,f27,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k7_relat_1(sK0,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,sK0),k1_relat_1(X1))
      | k7_relat_1(sK0,X0) = X1 ) ),
    inference(superposition,[],[f32,f52])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,X2),k1_relat_1(X1))
      | k7_relat_1(X2,X0) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f395,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(trivial_inequality_removal,[],[f393])).

fof(f393,plain,
    ( k1_funct_1(sK0,sK3) != k1_funct_1(sK0,sK3)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(superposition,[],[f45,f392])).

fof(f392,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK0,sK3)
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(backward_demodulation,[],[f380,f303])).

fof(f303,plain,
    ( k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f49,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | k1_funct_1(sK0,X0) = k1_funct_1(k7_relat_1(sK0,sK2),X0) ) ),
    inference(global_subsumption,[],[f26,f27,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | k1_funct_1(sK0,X0) = k1_funct_1(k7_relat_1(sK0,sK2),X0) ) ),
    inference(superposition,[],[f34,f56])).

fof(f49,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_4
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f380,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3)
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(resolution,[],[f330,f49])).

fof(f330,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | k1_funct_1(sK1,X4) = k1_funct_1(k7_relat_1(sK0,sK2),X4) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl5_36
  <=> ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | k1_funct_1(sK1,X4) = k1_funct_1(k7_relat_1(sK0,sK2),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f45,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_3
  <=> k1_funct_1(sK1,sK3) = k1_funct_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f377,plain,
    ( ~ spl5_15
    | ~ spl5_16
    | spl5_36
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f376,f36,f329,f119,f116])).

fof(f116,plain,
    ( spl5_15
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f119,plain,
    ( spl5_16
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f376,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,X4) = k1_funct_1(k7_relat_1(sK0,sK2),X4) )
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f370,f56])).

fof(f370,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(k7_relat_1(sK0,sK2)))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,X4) = k1_funct_1(k7_relat_1(sK0,sK2),X4) )
    | ~ spl5_1 ),
    inference(superposition,[],[f34,f37])).

fof(f37,plain,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f147,plain,
    ( ~ spl5_15
    | ~ spl5_16
    | spl5_12 ),
    inference(avatar_split_clause,[],[f146,f100,f119,f116])).

fof(f146,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_12 ),
    inference(resolution,[],[f101,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f101,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK2))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f141,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl5_16 ),
    inference(resolution,[],[f120,f25])).

fof(f120,plain,
    ( ~ v1_funct_1(sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f119])).

fof(f133,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl5_15 ),
    inference(resolution,[],[f117,f24])).

fof(f117,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f121,plain,
    ( ~ spl5_15
    | ~ spl5_16
    | spl5_11 ),
    inference(avatar_split_clause,[],[f114,f97,f119,f116])).

fof(f114,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_11 ),
    inference(resolution,[],[f98,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,sK2))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f84,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f74,f27])).

fof(f74,plain,
    ( ~ v1_funct_1(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f80,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f71,f26])).

fof(f71,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f50,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f19,f48,f36])).

fof(f19,plain,
    ( r2_hidden(sK3,sK2)
    | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f20,f44,f36])).

fof(f20,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3)
    | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f21,f39,f36])).

fof(f21,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK1,X3) = k1_funct_1(sK0,X3)
      | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (3908)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.47  % (3908)Refutation not found, incomplete strategy% (3908)------------------------------
% 0.20/0.47  % (3908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3908)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (3908)Memory used [KB]: 10618
% 0.20/0.47  % (3908)Time elapsed: 0.065 s
% 0.20/0.47  % (3908)------------------------------
% 0.20/0.47  % (3908)------------------------------
% 0.20/0.47  % (3913)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (3903)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (3898)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (3912)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (3901)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (3918)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (3901)Refutation not found, incomplete strategy% (3901)------------------------------
% 0.20/0.50  % (3901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3901)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3919)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (3901)Memory used [KB]: 10618
% 0.20/0.50  % (3901)Time elapsed: 0.090 s
% 0.20/0.50  % (3901)------------------------------
% 0.20/0.50  % (3901)------------------------------
% 0.20/0.50  % (3899)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (3904)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (3906)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (3914)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (3911)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (3921)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (3920)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (3910)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (3917)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (3907)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (3915)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.52  % (3900)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (3909)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (3905)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (3902)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.53  % (3905)Refutation not found, incomplete strategy% (3905)------------------------------
% 0.20/0.53  % (3905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3905)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3905)Memory used [KB]: 6140
% 0.20/0.53  % (3905)Time elapsed: 0.125 s
% 0.20/0.53  % (3905)------------------------------
% 0.20/0.53  % (3905)------------------------------
% 0.20/0.53  % (3921)Refutation not found, incomplete strategy% (3921)------------------------------
% 0.20/0.53  % (3921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3921)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3921)Memory used [KB]: 10618
% 0.20/0.53  % (3921)Time elapsed: 0.126 s
% 0.20/0.53  % (3921)------------------------------
% 0.20/0.53  % (3921)------------------------------
% 0.20/0.53  % (3916)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.54  % (3910)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f579,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f41,f46,f50,f80,f84,f121,f133,f141,f147,f377,f395,f413,f538,f573])).
% 0.20/0.54  fof(f573,plain,(
% 0.20/0.54    spl5_1 | ~spl5_30),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f572])).
% 0.20/0.54  fof(f572,plain,(
% 0.20/0.54    $false | (spl5_1 | ~spl5_30)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f562])).
% 0.20/0.54  fof(f562,plain,(
% 0.20/0.54    k7_relat_1(sK0,sK2) != k7_relat_1(sK0,sK2) | (spl5_1 | ~spl5_30)),
% 0.20/0.54    inference(superposition,[],[f42,f540])).
% 0.20/0.54  fof(f540,plain,(
% 0.20/0.54    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~spl5_30),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f539])).
% 0.20/0.54  fof(f539,plain,(
% 0.20/0.54    sK2 != sK2 | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~spl5_30),
% 0.20/0.54    inference(superposition,[],[f224,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 0.20/0.54    inference(global_subsumption,[],[f26,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ~v1_relat_1(sK0) | sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 0.20/0.54    inference(resolution,[],[f29,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    r1_tarski(sK2,k1_relat_1(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2))) & r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f8])).
% 0.20/0.54  fof(f8,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : ((k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <~> ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2))) & (r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f6])).
% 0.20/0.54  fof(f6,conjecture,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((r1_tarski(X2,k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) => (k7_relat_1(X0,X2) = k7_relat_1(X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    v1_relat_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f224,plain,(
% 0.20/0.54    ( ! [X1] : (sK2 != k1_relat_1(k7_relat_1(sK0,X1)) | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X1)) ) | ~spl5_30),
% 0.20/0.54    inference(avatar_component_clause,[],[f223])).
% 0.20/0.54  fof(f223,plain,(
% 0.20/0.54    spl5_30 <=> ! [X1] : (sK2 != k1_relat_1(k7_relat_1(sK0,X1)) | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) | spl5_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    spl5_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.54  fof(f538,plain,(
% 0.20/0.54    ~spl5_12 | ~spl5_8 | ~spl5_7 | ~spl5_11 | spl5_30 | ~spl5_2 | ~spl5_29),
% 0.20/0.54    inference(avatar_split_clause,[],[f537,f220,f39,f223,f97,f70,f73,f100])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    spl5_12 <=> v1_relat_1(k7_relat_1(sK1,sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    spl5_8 <=> v1_funct_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    spl5_7 <=> v1_relat_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    spl5_11 <=> v1_funct_1(k7_relat_1(sK1,sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    spl5_2 <=> ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK1,X3) = k1_funct_1(sK0,X3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.54  fof(f220,plain,(
% 0.20/0.54    spl5_29 <=> r2_hidden(sK4(k7_relat_1(sK1,sK2),sK0),sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.20/0.54  fof(f537,plain,(
% 0.20/0.54    ( ! [X0] : (sK2 != k1_relat_1(k7_relat_1(sK0,X0)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k7_relat_1(sK1,sK2)) | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X0)) ) | (~spl5_2 | ~spl5_29)),
% 0.20/0.54    inference(forward_demodulation,[],[f536,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X1] : (k1_relat_1(k7_relat_1(sK0,X1)) = k3_xboole_0(k1_relat_1(sK0),X1)) )),
% 0.20/0.54    inference(resolution,[],[f28,f26])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.54  fof(f536,plain,(
% 0.20/0.54    ( ! [X0] : (sK2 != k3_xboole_0(k1_relat_1(sK0),X0) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k7_relat_1(sK1,sK2)) | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X0)) ) | (~spl5_2 | ~spl5_29)),
% 0.20/0.54    inference(forward_demodulation,[],[f535,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    sK2 = k1_relat_1(k7_relat_1(sK1,sK2))),
% 0.20/0.54    inference(global_subsumption,[],[f24,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ~v1_relat_1(sK1) | sK2 = k1_relat_1(k7_relat_1(sK1,sK2))),
% 0.20/0.54    inference(resolution,[],[f29,f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    r1_tarski(sK2,k1_relat_1(sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    v1_relat_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f535,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k3_xboole_0(k1_relat_1(sK0),X0) != k1_relat_1(k7_relat_1(sK1,sK2)) | ~v1_relat_1(k7_relat_1(sK1,sK2)) | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X0)) ) | (~spl5_2 | ~spl5_29)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f534])).
% 0.20/0.54  fof(f534,plain,(
% 0.20/0.54    ( ! [X0] : (k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),sK0)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | k3_xboole_0(k1_relat_1(sK0),X0) != k1_relat_1(k7_relat_1(sK1,sK2)) | ~v1_relat_1(k7_relat_1(sK1,sK2)) | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X0)) ) | (~spl5_2 | ~spl5_29)),
% 0.20/0.54    inference(superposition,[],[f33,f523])).
% 0.20/0.54  fof(f523,plain,(
% 0.20/0.54    k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),sK0)) | (~spl5_2 | ~spl5_29)),
% 0.20/0.54    inference(forward_demodulation,[],[f241,f423])).
% 0.20/0.54  fof(f423,plain,(
% 0.20/0.54    k1_funct_1(sK1,sK4(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK4(k7_relat_1(sK1,sK2),sK0)) | (~spl5_2 | ~spl5_29)),
% 0.20/0.54    inference(resolution,[],[f221,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK1,X3) = k1_funct_1(sK0,X3)) ) | ~spl5_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f39])).
% 0.20/0.54  fof(f221,plain,(
% 0.20/0.54    r2_hidden(sK4(k7_relat_1(sK1,sK2),sK0),sK2) | ~spl5_29),
% 0.20/0.54    inference(avatar_component_clause,[],[f220])).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    k1_funct_1(sK1,sK4(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(k7_relat_1(sK1,sK2),sK4(k7_relat_1(sK1,sK2),sK0)) | ~spl5_29),
% 0.20/0.54    inference(resolution,[],[f221,f95])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_funct_1(sK1,X0) = k1_funct_1(k7_relat_1(sK1,sK2),X0)) )),
% 0.20/0.54    inference(global_subsumption,[],[f24,f25,f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(k7_relat_1(sK1,sK2),X0)) )),
% 0.20/0.54    inference(superposition,[],[f34,f57])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(flattening,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    v1_funct_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_funct_1(X1,sK4(X1,X2)) != k1_funct_1(X2,sK4(X1,X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_relat_1(X1) | k7_relat_1(X2,X0) = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).
% 0.20/0.54  fof(f413,plain,(
% 0.20/0.54    spl5_29 | ~spl5_12 | ~spl5_11 | spl5_30),
% 0.20/0.54    inference(avatar_split_clause,[],[f405,f223,f97,f100,f220])).
% 0.20/0.54  fof(f405,plain,(
% 0.20/0.54    ( ! [X11] : (sK2 != k1_relat_1(k7_relat_1(sK0,X11)) | ~v1_funct_1(k7_relat_1(sK1,sK2)) | ~v1_relat_1(k7_relat_1(sK1,sK2)) | r2_hidden(sK4(k7_relat_1(sK1,sK2),sK0),sK2) | k7_relat_1(sK1,sK2) = k7_relat_1(sK0,X11)) )),
% 0.20/0.54    inference(superposition,[],[f113,f57])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k7_relat_1(sK0,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,sK0),k1_relat_1(X1)) | k7_relat_1(sK0,X0) = X1) )),
% 0.20/0.54    inference(global_subsumption,[],[f26,f27,f112])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k7_relat_1(sK0,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,sK0),k1_relat_1(X1)) | k7_relat_1(sK0,X0) = X1) )),
% 0.20/0.54    inference(superposition,[],[f32,f52])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,X2),k1_relat_1(X1)) | k7_relat_1(X2,X0) = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    v1_funct_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f395,plain,(
% 0.20/0.54    spl5_3 | ~spl5_4 | ~spl5_36),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f394])).
% 0.20/0.54  fof(f394,plain,(
% 0.20/0.54    $false | (spl5_3 | ~spl5_4 | ~spl5_36)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f393])).
% 0.20/0.54  fof(f393,plain,(
% 0.20/0.54    k1_funct_1(sK0,sK3) != k1_funct_1(sK0,sK3) | (spl5_3 | ~spl5_4 | ~spl5_36)),
% 0.20/0.54    inference(superposition,[],[f45,f392])).
% 0.20/0.54  fof(f392,plain,(
% 0.20/0.54    k1_funct_1(sK1,sK3) = k1_funct_1(sK0,sK3) | (~spl5_4 | ~spl5_36)),
% 0.20/0.54    inference(backward_demodulation,[],[f380,f303])).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    k1_funct_1(sK0,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3) | ~spl5_4),
% 0.20/0.54    inference(resolution,[],[f49,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | k1_funct_1(sK0,X0) = k1_funct_1(k7_relat_1(sK0,sK2),X0)) )),
% 0.20/0.54    inference(global_subsumption,[],[f26,f27,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_funct_1(sK0,X0) = k1_funct_1(k7_relat_1(sK0,sK2),X0)) )),
% 0.20/0.54    inference(superposition,[],[f34,f56])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    r2_hidden(sK3,sK2) | ~spl5_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    spl5_4 <=> r2_hidden(sK3,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.54  fof(f380,plain,(
% 0.20/0.54    k1_funct_1(sK1,sK3) = k1_funct_1(k7_relat_1(sK0,sK2),sK3) | (~spl5_4 | ~spl5_36)),
% 0.20/0.54    inference(resolution,[],[f330,f49])).
% 0.20/0.54  fof(f330,plain,(
% 0.20/0.54    ( ! [X4] : (~r2_hidden(X4,sK2) | k1_funct_1(sK1,X4) = k1_funct_1(k7_relat_1(sK0,sK2),X4)) ) | ~spl5_36),
% 0.20/0.54    inference(avatar_component_clause,[],[f329])).
% 0.20/0.54  fof(f329,plain,(
% 0.20/0.54    spl5_36 <=> ! [X4] : (~r2_hidden(X4,sK2) | k1_funct_1(sK1,X4) = k1_funct_1(k7_relat_1(sK0,sK2),X4))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3) | spl5_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    spl5_3 <=> k1_funct_1(sK1,sK3) = k1_funct_1(sK0,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.54  fof(f377,plain,(
% 0.20/0.54    ~spl5_15 | ~spl5_16 | spl5_36 | ~spl5_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f376,f36,f329,f119,f116])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    spl5_15 <=> v1_relat_1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    spl5_16 <=> v1_funct_1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.54  fof(f376,plain,(
% 0.20/0.54    ( ! [X4] : (~r2_hidden(X4,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X4) = k1_funct_1(k7_relat_1(sK0,sK2),X4)) ) | ~spl5_1),
% 0.20/0.54    inference(forward_demodulation,[],[f370,f56])).
% 0.20/0.54  fof(f370,plain,(
% 0.20/0.54    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(k7_relat_1(sK0,sK2))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X4) = k1_funct_1(k7_relat_1(sK0,sK2),X4)) ) | ~spl5_1),
% 0.20/0.54    inference(superposition,[],[f34,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) | ~spl5_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f36])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ~spl5_15 | ~spl5_16 | spl5_12),
% 0.20/0.54    inference(avatar_split_clause,[],[f146,f100,f119,f116])).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl5_12),
% 0.20/0.54    inference(resolution,[],[f101,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    ~v1_relat_1(k7_relat_1(sK1,sK2)) | spl5_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f100])).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    spl5_16),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    $false | spl5_16),
% 0.20/0.54    inference(resolution,[],[f120,f25])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    ~v1_funct_1(sK1) | spl5_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f119])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    spl5_15),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f132])).
% 0.20/0.54  fof(f132,plain,(
% 0.20/0.54    $false | spl5_15),
% 0.20/0.54    inference(resolution,[],[f117,f24])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ~v1_relat_1(sK1) | spl5_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f116])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ~spl5_15 | ~spl5_16 | spl5_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f114,f97,f119,f116])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl5_11),
% 0.20/0.54    inference(resolution,[],[f98,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    ~v1_funct_1(k7_relat_1(sK1,sK2)) | spl5_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f97])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    spl5_8),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f83])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    $false | spl5_8),
% 0.20/0.54    inference(resolution,[],[f74,f27])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ~v1_funct_1(sK0) | spl5_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f73])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    spl5_7),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    $false | spl5_7),
% 0.20/0.54    inference(resolution,[],[f71,f26])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ~v1_relat_1(sK0) | spl5_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f70])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ~spl5_1 | spl5_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f19,f48,f36])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    r2_hidden(sK3,sK2) | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ~spl5_1 | ~spl5_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f20,f44,f36])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    k1_funct_1(sK1,sK3) != k1_funct_1(sK0,sK3) | k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    spl5_1 | spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f21,f39,f36])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK1,X3) = k1_funct_1(sK0,X3) | k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (3910)------------------------------
% 0.20/0.54  % (3910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3910)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (3910)Memory used [KB]: 11129
% 0.20/0.54  % (3910)Time elapsed: 0.127 s
% 0.20/0.54  % (3910)------------------------------
% 0.20/0.54  % (3910)------------------------------
% 0.20/0.54  % (3897)Success in time 0.186 s
%------------------------------------------------------------------------------
