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
% DateTime   : Thu Dec  3 12:54:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 234 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :    8
%              Number of atoms          :  326 (1037 expanded)
%              Number of equality atoms :   77 ( 319 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26173)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f361,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f124,f129,f138,f331,f353,f359,f360])).

fof(f360,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))
    | k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))
    | k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f359,plain,
    ( spl4_30
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f341,f321,f355])).

fof(f355,plain,
    ( spl4_30
  <=> k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f321,plain,
    ( spl4_26
  <=> r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f341,plain,
    ( k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))
    | ~ spl4_26 ),
    inference(resolution,[],[f323,f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

fof(f323,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f321])).

fof(f353,plain,
    ( spl4_29
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f335,f321,f58,f53,f350])).

fof(f350,plain,
    ( spl4_29
  <=> k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f53,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f58,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f335,plain,
    ( k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f60,f55,f323,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f55,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f331,plain,
    ( spl4_26
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f305,f136,f121,f321])).

fof(f121,plain,
    ( spl4_9
  <=> r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f136,plain,
    ( spl4_12
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3))
        | r2_hidden(X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f305,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2)
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(resolution,[],[f123,f137])).

fof(f137,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3))
        | r2_hidden(X4,X3) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f123,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f138,plain,
    ( ~ spl4_4
    | spl4_12
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f118,f58,f48,f136,f58])).

fof(f48,plain,
    ( spl4_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f118,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3))
        | r2_hidden(X4,X3)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f34,f80])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f129,plain,
    ( ~ spl4_10
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f113,f68,f63,f58,f53,f48,f43,f126])).

fof(f126,plain,
    ( spl4_10
  <=> k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

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

fof(f113,plain,
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
      ( k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2))
      | k7_relat_1(X2,X0) = X1
      | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0)
      | ~ v1_funct_1(X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

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

fof(f124,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f119,f68,f63,f58,f53,f48,f43,f121])).

fof(f119,plain,
    ( r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f114,f80])).

fof(f114,plain,
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (26168)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (26163)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (26171)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (26170)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (26166)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (26181)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (26185)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (26182)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (26180)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (26184)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (26167)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (26165)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (26164)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (26165)Refutation not found, incomplete strategy% (26165)------------------------------
% 0.21/0.51  % (26165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26165)Memory used [KB]: 10618
% 0.21/0.51  % (26165)Time elapsed: 0.094 s
% 0.21/0.51  % (26165)------------------------------
% 0.21/0.51  % (26165)------------------------------
% 0.21/0.51  % (26183)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (26162)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (26185)Refutation not found, incomplete strategy% (26185)------------------------------
% 0.21/0.51  % (26185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26185)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26185)Memory used [KB]: 10618
% 0.21/0.51  % (26185)Time elapsed: 0.064 s
% 0.21/0.51  % (26185)------------------------------
% 0.21/0.51  % (26185)------------------------------
% 0.21/0.51  % (26177)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (26168)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (26173)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  fof(f361,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f124,f129,f138,f331,f353,f359,f360])).
% 0.21/0.51  fof(f360,plain,(
% 0.21/0.51    k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) | k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) | k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    spl4_30 | ~spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f341,f321,f355])).
% 0.21/0.51  fof(f355,plain,(
% 0.21/0.51    spl4_30 <=> k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    spl4_26 <=> r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) | ~spl4_26),
% 0.21/0.51    inference(resolution,[],[f323,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,sK2) | k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ((k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f20,f19,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (k7_relat_1(X1,X2) != k7_relat_1(sK0,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(sK0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X2] : (k7_relat_1(sK0,X2) != k7_relat_1(sK1,X2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(sK0) = k1_relat_1(sK1)) => (k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) & ! [X3] : (k1_funct_1(sK0,X3) = k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK2)) & k1_relat_1(sK0) = k1_relat_1(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (k7_relat_1(X0,X2) != k7_relat_1(X1,X2) & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X0,X3) | ~r2_hidden(X3,X2)) & k1_relat_1(X1) = k1_relat_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((! [X3] : (r2_hidden(X3,X2) => k1_funct_1(X1,X3) = k1_funct_1(X0,X3)) & k1_relat_1(X1) = k1_relat_1(X0)) => k7_relat_1(X0,X2) = k7_relat_1(X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2) | ~spl4_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f321])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    spl4_29 | ~spl4_3 | ~spl4_4 | ~spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f335,f321,f58,f53,f350])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    spl4_29 <=> k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl4_3 <=> v1_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl4_4 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK1,sK3(k7_relat_1(sK1,sK2),sK0)) | (~spl4_3 | ~spl4_4 | ~spl4_26)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f60,f55,f323,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v1_funct_1(sK1) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f53])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    spl4_26 | ~spl4_9 | ~spl4_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f305,f136,f121,f321])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl4_9 <=> r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl4_12 <=> ! [X3,X4] : (~r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3)) | r2_hidden(X4,X3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),sK2) | (~spl4_9 | ~spl4_12)),
% 0.21/0.51    inference(resolution,[],[f123,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3)) | r2_hidden(X4,X3)) ) | ~spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f136])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2)) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ~spl4_4 | spl4_12 | ~spl4_2 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f118,f58,f48,f136,f58])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    spl4_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~r2_hidden(X4,k3_xboole_0(k1_relat_1(sK0),X3)) | r2_hidden(X4,X3) | ~v1_relat_1(sK1)) ) | (~spl4_2 | ~spl4_4)),
% 0.21/0.51    inference(superposition,[],[f34,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) ) | (~spl4_2 | ~spl4_4)),
% 0.21/0.51    inference(forward_demodulation,[],[f76,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f48])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl4_4),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f60,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~spl4_10 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f113,f68,f63,f58,f53,f48,f43,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl4_10 <=> k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) = k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    spl4_1 <=> k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl4_5 <=> v1_funct_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl4_6 <=> v1_relat_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    k1_funct_1(k7_relat_1(sK1,sK2),sK3(k7_relat_1(sK1,sK2),sK0)) != k1_funct_1(sK0,sK3(k7_relat_1(sK1,sK2),sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f65,f72,f74,f45,f80,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) | k7_relat_1(X2,X0) = X1 | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | (k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X2,X1] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK3(X1,X2)) != k1_funct_1(X2,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_relat_1(X2,X0) = X1 | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((k7_relat_1(X2,X0) = X1 | (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X2,X3) & r2_hidden(X3,k1_relat_1(X1))) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k1_relat_1(X1) = k3_xboole_0(k1_relat_1(X2),X0)) => k7_relat_1(X2,X0) = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_funct_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f43])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k7_relat_1(sK1,X0))) ) | (~spl4_3 | ~spl4_4)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f60,f55,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl4_3 | ~spl4_4)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f60,f55,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    v1_funct_1(sK0) | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f63])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    v1_relat_1(sK0) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl4_9 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f68,f63,f58,f53,f48,f43,f121])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k3_xboole_0(k1_relat_1(sK0),sK2)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f114,f80])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    r2_hidden(sK3(k7_relat_1(sK1,sK2),sK0),k1_relat_1(k7_relat_1(sK1,sK2))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f65,f72,f74,f45,f80,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | r2_hidden(sK3(X1,X2),k1_relat_1(X1)) | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(X2),X0) | k7_relat_1(X2,X0) = X1 | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f68])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f58])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f53])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f48])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f43])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26168)------------------------------
% 0.21/0.51  % (26168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26168)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26168)Memory used [KB]: 11001
% 0.21/0.51  % (26168)Time elapsed: 0.099 s
% 0.21/0.51  % (26168)------------------------------
% 0.21/0.51  % (26168)------------------------------
% 0.21/0.51  % (26161)Success in time 0.153 s
%------------------------------------------------------------------------------
