%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 246 expanded)
%              Number of leaves         :   21 ( 108 expanded)
%              Depth                    :    9
%              Number of atoms          :  347 (1077 expanded)
%              Number of equality atoms :   76 ( 330 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f517,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f138,f143,f152,f435,f476,f516])).

fof(f516,plain,
    ( ~ spl4_4
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_2
    | ~ spl4_4
    | spl4_12
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f515,f472,f140,f58,f48,f135,f53,f58])).

fof(f53,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f135,plain,
    ( spl4_11
  <=> r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f48,plain,
    ( spl4_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f58,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f140,plain,
    ( spl4_12
  <=> k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f472,plain,
    ( spl4_32
  <=> k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f515,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_12
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f514,f80])).

fof(f80,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f76,f50])).

fof(f50,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f76,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f60,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f514,plain,
    ( ~ r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_12
    | ~ spl4_32 ),
    inference(trivial_inequality_removal,[],[f513])).

fof(f513,plain,
    ( k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0))
    | ~ r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_12
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f512,f474])).

fof(f474,plain,
    ( k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f472])).

fof(f512,plain,
    ( k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))
    | ~ r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_12 ),
    inference(superposition,[],[f142,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f142,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f476,plain,
    ( spl4_32
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f469,f425,f472])).

fof(f425,plain,
    ( spl4_28
  <=> r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f469,plain,
    ( k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))
    | ~ spl4_28 ),
    inference(resolution,[],[f427,f31])).

fof(f31,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & ! [X3] :
        ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK2) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & ! [X3] :
                    ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                    | ~ r2_hidden(X3,X2) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(sK0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k7_relat_1(X1,X2) != k7_relat_1(sK0,X2)
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(sK0,X3)
                | ~ r2_hidden(X3,X2) )
            & k1_relat_1(X1) = k1_relat_1(sK0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
          & ! [X3] :
              ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
              | ~ r2_hidden(X3,X2) )
          & k1_relat_1(sK0) = k1_relat_1(sK1) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2)
        & ! [X3] :
            ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
            | ~ r2_hidden(X3,X2) )
        & k1_relat_1(sK0) = k1_relat_1(sK1) )
   => ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
      & ! [X3] :
          ( k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)
          | ~ r2_hidden(X3,sK2) )
      & k1_relat_1(sK0) = k1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X0,X3)
                  | ~ r2_hidden(X3,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
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
                ( ( ! [X3] :
                      ( r2_hidden(X3,X2)
                     => k1_funct_1(X1,X3) = k1_funct_1(X0,X3) )
                  & k1_relat_1(X1) = k1_relat_1(X0) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( ! [X3] :
                    ( r2_hidden(X3,X2)
                   => k1_funct_1(X1,X3) = k1_funct_1(X0,X3) )
                & k1_relat_1(X1) = k1_relat_1(X0) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

fof(f427,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f425])).

fof(f435,plain,
    ( spl4_28
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f420,f150,f135,f425])).

fof(f150,plain,
    ( spl4_14
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3))
        | r2_hidden(X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f420,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2)
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(resolution,[],[f137,f151])).

fof(f151,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3))
        | r2_hidden(X4,X3) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f137,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f152,plain,
    ( ~ spl4_4
    | spl4_14
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f132,f58,f48,f150,f58])).

fof(f132,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3))
        | r2_hidden(X4,X3)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f34,f80])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f143,plain,
    ( ~ spl4_12
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f127,f68,f63,f58,f53,f48,f43,f140])).

fof(f43,plain,
    ( spl4_1
  <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,
    ( spl4_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( spl4_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f127,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f70,f65,f72,f74,f45,f80,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | k7_relat_1(X2,X0) = X1
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(X2,X0) = X1
          | ( k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2))
            & r2_hidden(sK3(X1,X2),k1_relat_1(X1)) )
          | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f24])).

fof(f24,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2))
        & r2_hidden(sK3(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f45,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f74,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK1,X0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f60,f55,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f55,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f72,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f60,f55,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f70,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f138,plain,
    ( spl4_11
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f133,f68,f63,f58,f53,f48,f43,f135])).

fof(f133,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f128,f80])).

fof(f128,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f70,f65,f72,f74,f45,f80,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | r2_hidden(sK3(X1,X2),k1_relat_1(X1))
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | k7_relat_1(X2,X0) = X1
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f43])).

fof(f32,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (11267)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.48  % (11283)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.49  % (11272)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (11268)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (11275)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.50  % (11271)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (11270)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (11268)Refutation not found, incomplete strategy% (11268)------------------------------
% 0.22/0.50  % (11268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11269)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (11268)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11268)Memory used [KB]: 10618
% 0.22/0.50  % (11268)Time elapsed: 0.085 s
% 0.22/0.50  % (11268)------------------------------
% 0.22/0.50  % (11268)------------------------------
% 0.22/0.50  % (11265)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (11266)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (11276)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.51  % (11284)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (11280)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (11287)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (11286)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (11273)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (11279)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (11278)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (11282)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (11285)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (11288)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (11281)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.53  % (11288)Refutation not found, incomplete strategy% (11288)------------------------------
% 0.22/0.53  % (11288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11288)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11288)Memory used [KB]: 10618
% 0.22/0.53  % (11288)Time elapsed: 0.008 s
% 0.22/0.53  % (11288)------------------------------
% 0.22/0.53  % (11288)------------------------------
% 0.22/0.53  % (11271)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f517,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f138,f143,f152,f435,f476,f516])).
% 0.22/0.53  fof(f516,plain,(
% 0.22/0.53    ~spl4_4 | ~spl4_3 | ~spl4_11 | ~spl4_2 | ~spl4_4 | spl4_12 | ~spl4_32),
% 0.22/0.53    inference(avatar_split_clause,[],[f515,f472,f140,f58,f48,f135,f53,f58])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl4_3 <=> v1_funct_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl4_11 <=> r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    spl4_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    spl4_4 <=> v1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    spl4_12 <=> k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.53  fof(f472,plain,(
% 0.22/0.53    spl4_32 <=> k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.53  fof(f515,plain,(
% 0.22/0.53    ~r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_2 | ~spl4_4 | spl4_12 | ~spl4_32)),
% 0.22/0.53    inference(forward_demodulation,[],[f514,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) ) | (~spl4_2 | ~spl4_4)),
% 0.22/0.53    inference(forward_demodulation,[],[f76,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f48])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl4_4),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f60,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    v1_relat_1(sK1) | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f58])).
% 0.22/0.53  fof(f514,plain,(
% 0.22/0.53    ~r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl4_12 | ~spl4_32)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f513])).
% 0.22/0.53  fof(f513,plain,(
% 0.22/0.53    k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) | ~r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl4_12 | ~spl4_32)),
% 0.22/0.53    inference(forward_demodulation,[],[f512,f474])).
% 0.22/0.53  fof(f474,plain,(
% 0.22/0.53    k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) | ~spl4_32),
% 0.22/0.53    inference(avatar_component_clause,[],[f472])).
% 0.22/0.53  fof(f512,plain,(
% 0.22/0.53    k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) | ~r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_12),
% 0.22/0.53    inference(superposition,[],[f142,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) | spl4_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f140])).
% 0.22/0.53  fof(f476,plain,(
% 0.22/0.53    spl4_32 | ~spl4_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f469,f425,f472])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    spl4_28 <=> r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.53  fof(f469,plain,(
% 0.22/0.53    k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) | ~spl4_28),
% 0.22/0.53    inference(resolution,[],[f427,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f20,f19,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.22/0.53    inference(negated_conjecture,[],[f6])).
% 0.22/0.53  fof(f6,conjecture,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).
% 0.22/0.53  fof(f427,plain,(
% 0.22/0.53    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2) | ~spl4_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f425])).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    spl4_28 | ~spl4_11 | ~spl4_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f420,f150,f135,f425])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    spl4_14 <=> ! [X3,X4] : (~r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3)) | r2_hidden(X4,X3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.53  fof(f420,plain,(
% 0.22/0.53    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2) | (~spl4_11 | ~spl4_14)),
% 0.22/0.53    inference(resolution,[],[f137,f151])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3)) | r2_hidden(X4,X3)) ) | ~spl4_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f150])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2)) | ~spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f135])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ~spl4_4 | spl4_14 | ~spl4_2 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f132,f58,f48,f150,f58])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X4,X3] : (~r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3)) | r2_hidden(X4,X3) | ~v1_relat_1(sK1)) ) | (~spl4_2 | ~spl4_4)),
% 0.22/0.53    inference(superposition,[],[f34,f80])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ~spl4_12 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f127,f68,f63,f58,f53,f48,f43,f140])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    spl4_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl4_5 <=> v1_funct_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl4_6 <=> v1_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f70,f65,f72,f74,f45,f80,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | k7_relat_1(X2,X0) = X1 | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | (k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X2,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f43])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(k7_relat_1(sK1,X0))) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f60,f55,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    v1_funct_1(sK1) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f53])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl4_3 | ~spl4_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f60,f55,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    v1_funct_1(sK0) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    v1_relat_1(sK0) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f68])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    spl4_11 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f133,f68,f63,f58,f53,f48,f43,f135])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.22/0.53    inference(forward_demodulation,[],[f128,f80])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f70,f65,f72,f74,f45,f80,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | r2_hidden(sK3(X1,X2),k1_relat_1(X1)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | k7_relat_1(X2,X0) = X1 | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f68])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f63])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v1_funct_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f58])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f53])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f48])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ~spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f43])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (11271)------------------------------
% 0.22/0.53  % (11271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11271)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (11271)Memory used [KB]: 11129
% 0.22/0.53  % (11271)Time elapsed: 0.116 s
% 0.22/0.53  % (11271)------------------------------
% 0.22/0.53  % (11271)------------------------------
% 0.22/0.53  % (11274)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  % (11264)Success in time 0.171 s
%------------------------------------------------------------------------------
