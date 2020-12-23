%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t39_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 81.45s
% Output     : Refutation 81.45s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 172 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  402 ( 616 expanded)
%              Number of equality atoms :   30 (  53 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119037,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f156,f163,f170,f21510,f21632,f22115,f22116,f23179,f74094,f119034])).

fof(f119034,plain,
    ( ~ spl6_1041
    | ~ spl6_6
    | spl6_53
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f119003,f558,f551,f168,f10228])).

fof(f10228,plain,
    ( spl6_1041
  <=> ~ r2_hidden(k4_tarski(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1041])])).

fof(f168,plain,
    ( spl6_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f551,plain,
    ( spl6_53
  <=> ~ r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),k3_relat_1(k2_wellord1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f558,plain,
    ( spl6_54
  <=> r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f119003,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0)))),sK1)
    | ~ spl6_6
    | ~ spl6_53
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f559,f559,f3911,f1415])).

fof(f1415,plain,
    ( ! [X21,X19,X20] :
        ( ~ r2_hidden(k4_tarski(X19,X20),sK1)
        | r2_hidden(k4_tarski(X19,X20),k2_wellord1(sK1,X21))
        | ~ r2_hidden(X20,X21)
        | ~ r2_hidden(X19,X21) )
    | ~ spl6_6 ),
    inference(resolution,[],[f385,f137])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',t106_zfmisc_1)).

fof(f385,plain,
    ( ! [X10,X9] :
        ( ~ r2_hidden(X10,k2_zfmisc_1(X9,X9))
        | r2_hidden(X10,k2_wellord1(sK1,X9))
        | ~ r2_hidden(X10,sK1) )
    | ~ spl6_6 ),
    inference(superposition,[],[f140,f181])).

fof(f181,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f169,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',d6_wellord1)).

fof(f169,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f168])).

fof(f140,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f81,f82])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',d4_xboole_0)).

fof(f3911,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),X0),k2_wellord1(sK1,sK0))
    | ~ spl6_6
    | ~ spl6_53 ),
    inference(unit_resulting_resolution,[],[f182,f552,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',t30_relat_1)).

fof(f552,plain,
    ( ~ r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),k3_relat_1(k2_wellord1(sK1,sK0)))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f551])).

fof(f182,plain,
    ( ! [X0] : v1_relat_1(k2_wellord1(sK1,X0))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f169,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',dt_k2_wellord1)).

fof(f559,plain,
    ( r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),sK0)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f558])).

fof(f74094,plain,
    ( spl6_1040
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_290 ),
    inference(avatar_split_clause,[],[f73642,f2789,f232,f168,f10225])).

fof(f10225,plain,
    ( spl6_1040
  <=> r2_hidden(k4_tarski(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1040])])).

fof(f232,plain,
    ( spl6_16
  <=> v1_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f2789,plain,
    ( spl6_290
  <=> r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_290])])).

fof(f73642,plain,
    ( r2_hidden(k4_tarski(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0)))),sK1)
    | ~ spl6_6
    | ~ spl6_16
    | ~ spl6_290 ),
    inference(unit_resulting_resolution,[],[f169,f233,f2790,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f65,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK2(X0)),X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',l1_wellord1)).

fof(f2790,plain,
    ( r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),k3_relat_1(sK1))
    | ~ spl6_290 ),
    inference(avatar_component_clause,[],[f2789])).

fof(f233,plain,
    ( v1_relat_2(sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f232])).

fof(f23179,plain,
    ( spl6_290
    | ~ spl6_2
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f23118,f558,f154,f2789])).

fof(f154,plain,
    ( spl6_2
  <=> r1_tarski(sK0,k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f23118,plain,
    ( r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),k3_relat_1(sK1))
    | ~ spl6_2
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f155,f559,f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f75,f76])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',d3_tarski)).

fof(f155,plain,
    ( r1_tarski(sK0,k3_relat_1(sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f154])).

fof(f22116,plain,
    ( spl6_54
    | spl6_31 ),
    inference(avatar_split_clause,[],[f22110,f321,f558])).

fof(f321,plain,
    ( spl6_31
  <=> ~ r1_tarski(sK0,k3_relat_1(k2_wellord1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f22110,plain,
    ( r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),sK0)
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f322,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f322,plain,
    ( ~ r1_tarski(sK0,k3_relat_1(k2_wellord1(sK1,sK0)))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f321])).

fof(f22115,plain,
    ( ~ spl6_53
    | spl6_31 ),
    inference(avatar_split_clause,[],[f22111,f321,f551])).

fof(f22111,plain,
    ( ~ r2_hidden(sK4(sK0,k3_relat_1(k2_wellord1(sK1,sK0))),k3_relat_1(k2_wellord1(sK1,sK0)))
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f322,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f21632,plain,
    ( ~ spl6_31
    | spl6_1
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f21608,f168,f147,f321])).

fof(f147,plain,
    ( spl6_1
  <=> k3_relat_1(k2_wellord1(sK1,sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f21608,plain,
    ( ~ r1_tarski(sK0,k3_relat_1(k2_wellord1(sK1,sK0)))
    | ~ spl6_1
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f148,f184,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',d10_xboole_0)).

fof(f184,plain,
    ( ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f169,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',t20_wellord1)).

fof(f148,plain,
    ( k3_relat_1(k2_wellord1(sK1,sK0)) != sK0
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f21510,plain,
    ( spl6_16
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f21482,f168,f161,f232])).

fof(f161,plain,
    ( spl6_4
  <=> v2_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f21482,plain,
    ( v1_relat_2(sK1)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f162,f169,f97])).

fof(f97,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',d4_wellord1)).

fof(f162,plain,
    ( v2_wellord1(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f170,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f86,f168])).

fof(f86,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( k3_relat_1(k2_wellord1(sK1,sK0)) != sK0
    & r1_tarski(sK0,k3_relat_1(sK1))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f62])).

fof(f62,plain,
    ( ? [X0,X1] :
        ( k3_relat_1(k2_wellord1(X1,X0)) != X0
        & r1_tarski(X0,k3_relat_1(X1))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( k3_relat_1(k2_wellord1(sK1,sK0)) != sK0
      & r1_tarski(sK0,k3_relat_1(sK1))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) != X0
      & r1_tarski(X0,k3_relat_1(X1))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) != X0
      & r1_tarski(X0,k3_relat_1(X1))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( ( r1_tarski(X0,k3_relat_1(X1))
            & v2_wellord1(X1) )
         => k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t39_wellord1.p',t39_wellord1)).

fof(f163,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f87,f161])).

fof(f87,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f156,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f88,f154])).

fof(f88,plain,(
    r1_tarski(sK0,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f63])).

fof(f149,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f89,f147])).

fof(f89,plain,(
    k3_relat_1(k2_wellord1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
