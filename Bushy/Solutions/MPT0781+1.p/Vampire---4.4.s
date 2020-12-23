%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t30_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 247 expanded)
%              Number of leaves         :   13 (  64 expanded)
%              Depth                    :   19
%              Number of atoms          :  317 (1118 expanded)
%              Number of equality atoms :   50 ( 234 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7909,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7889,f7896,f7905])).

fof(f7905,plain,
    ( ~ spl5_40
    | spl5_43 ),
    inference(avatar_contradiction_clause,[],[f7904])).

fof(f7904,plain,
    ( $false
    | ~ spl5_40
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f7903,f63])).

fof(f63,plain,(
    k2_wellord1(sK0,k3_relat_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( k2_wellord1(sK0,k3_relat_1(sK0)) != sK0
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( k2_wellord1(X0,k3_relat_1(X0)) != X0
        & v1_relat_1(X0) )
   => ( k2_wellord1(sK0,k3_relat_1(sK0)) != sK0
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t30_wellord1.p',t30_wellord1)).

fof(f7903,plain,
    ( k2_wellord1(sK0,k3_relat_1(sK0)) = sK0
    | ~ spl5_40
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f7899,f7877])).

fof(f7877,plain,
    ( v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f7876])).

fof(f7876,plain,
    ( spl5_40
  <=> v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f7899,plain,
    ( ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | k2_wellord1(sK0,k3_relat_1(sK0)) = sK0
    | ~ spl5_43 ),
    inference(resolution,[],[f7886,f700])).

fof(f700,plain,(
    ! [X5] :
      ( r2_hidden(sK1(sK0,k2_wellord1(sK0,X5)),k3_relat_1(sK0))
      | ~ v1_relat_1(k2_wellord1(sK0,X5))
      | k2_wellord1(sK0,X5) = sK0 ) ),
    inference(subsumption_resolution,[],[f698,f62])).

fof(f62,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f698,plain,(
    ! [X5] :
      ( k2_wellord1(sK0,X5) = sK0
      | ~ v1_relat_1(k2_wellord1(sK0,X5))
      | r2_hidden(sK1(sK0,k2_wellord1(sK0,X5)),k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f477,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t30_wellord1.p',t30_relat_1)).

fof(f477,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(sK0,k2_wellord1(sK0,X0)),sK2(sK0,k2_wellord1(sK0,X0))),sK0)
      | k2_wellord1(sK0,X0) = sK0
      | ~ v1_relat_1(k2_wellord1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f468,f62])).

fof(f468,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(sK0,k2_wellord1(sK0,X0)),sK2(sK0,k2_wellord1(sK0,X0))),sK0)
      | k2_wellord1(sK0,X0) = sK0
      | ~ v1_relat_1(k2_wellord1(sK0,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(factoring,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,k2_wellord1(sK0,X1)),sK2(X0,k2_wellord1(sK0,X1))),sK0)
      | r2_hidden(k4_tarski(sK1(X0,k2_wellord1(sK0,X1)),sK2(X0,k2_wellord1(sK0,X1))),X0)
      | k2_wellord1(sK0,X1) = X0
      | ~ v1_relat_1(k2_wellord1(sK0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f103,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t30_wellord1.p',d2_relat_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_wellord1(sK0,X0))
      | r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f99,f102])).

fof(f102,plain,(
    ! [X0] : k2_wellord1(sK0,X0) = k3_xboole_0(sK0,k2_zfmisc_1(X0,X0)) ),
    inference(resolution,[],[f62,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t30_wellord1.p',d6_wellord1)).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t30_wellord1.p',d4_xboole_0)).

fof(f7886,plain,
    ( ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f7885])).

fof(f7885,plain,
    ( spl5_43
  <=> ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f7896,plain,(
    spl5_41 ),
    inference(avatar_contradiction_clause,[],[f7895])).

fof(f7895,plain,
    ( $false
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f7894,f62])).

fof(f7894,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl5_41 ),
    inference(resolution,[],[f7880,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t30_wellord1.p',dt_k2_wellord1)).

fof(f7880,plain,
    ( ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f7879])).

fof(f7879,plain,
    ( spl5_41
  <=> ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f7889,plain,
    ( ~ spl5_41
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f7888,f7885,f7879])).

fof(f7888,plain,
    ( ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0))) ),
    inference(subsumption_resolution,[],[f7865,f63])).

fof(f7865,plain,
    ( ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | k2_wellord1(sK0,k3_relat_1(sK0)) = sK0
    | ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f7857])).

fof(f7857,plain,
    ( ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,k3_relat_1(sK0))),k3_relat_1(sK0))
    | k2_wellord1(sK0,k3_relat_1(sK0)) = sK0
    | ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | ~ v1_relat_1(k2_wellord1(sK0,k3_relat_1(sK0)))
    | k2_wellord1(sK0,k3_relat_1(sK0)) = sK0 ),
    inference(resolution,[],[f5394,f701])).

fof(f701,plain,(
    ! [X6] :
      ( r2_hidden(sK2(sK0,k2_wellord1(sK0,X6)),k3_relat_1(sK0))
      | ~ v1_relat_1(k2_wellord1(sK0,X6))
      | k2_wellord1(sK0,X6) = sK0 ) ),
    inference(subsumption_resolution,[],[f699,f62])).

fof(f699,plain,(
    ! [X6] :
      ( k2_wellord1(sK0,X6) = sK0
      | ~ v1_relat_1(k2_wellord1(sK0,X6))
      | r2_hidden(sK2(sK0,k2_wellord1(sK0,X6)),k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f477,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5394,plain,(
    ! [X44] :
      ( ~ r2_hidden(sK2(sK0,k2_wellord1(sK0,X44)),X44)
      | ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,X44)),X44)
      | k2_wellord1(sK0,X44) = sK0
      | ~ v1_relat_1(k2_wellord1(sK0,X44)) ) ),
    inference(subsumption_resolution,[],[f5393,f477])).

fof(f5393,plain,(
    ! [X44] :
      ( ~ r2_hidden(sK2(sK0,k2_wellord1(sK0,X44)),X44)
      | ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,X44)),X44)
      | k2_wellord1(sK0,X44) = sK0
      | ~ r2_hidden(k4_tarski(sK1(sK0,k2_wellord1(sK0,X44)),sK2(sK0,k2_wellord1(sK0,X44))),sK0)
      | ~ v1_relat_1(k2_wellord1(sK0,X44)) ) ),
    inference(subsumption_resolution,[],[f5357,f62])).

fof(f5357,plain,(
    ! [X44] :
      ( ~ r2_hidden(sK2(sK0,k2_wellord1(sK0,X44)),X44)
      | ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,X44)),X44)
      | k2_wellord1(sK0,X44) = sK0
      | ~ r2_hidden(k4_tarski(sK1(sK0,k2_wellord1(sK0,X44)),sK2(sK0,k2_wellord1(sK0,X44))),sK0)
      | ~ v1_relat_1(k2_wellord1(sK0,X44))
      | ~ v1_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f5356])).

fof(f5356,plain,(
    ! [X44] :
      ( ~ r2_hidden(sK2(sK0,k2_wellord1(sK0,X44)),X44)
      | ~ r2_hidden(sK1(sK0,k2_wellord1(sK0,X44)),X44)
      | k2_wellord1(sK0,X44) = sK0
      | ~ r2_hidden(k4_tarski(sK1(sK0,k2_wellord1(sK0,X44)),sK2(sK0,k2_wellord1(sK0,X44))),sK0)
      | ~ v1_relat_1(k2_wellord1(sK0,X44))
      | ~ v1_relat_1(sK0)
      | k2_wellord1(sK0,X44) = sK0
      | ~ v1_relat_1(k2_wellord1(sK0,X44)) ) ),
    inference(resolution,[],[f127,f477])).

fof(f127,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(sK1(X6,k2_wellord1(sK0,X7)),sK2(X6,k2_wellord1(sK0,X7))),sK0)
      | ~ r2_hidden(sK2(X6,k2_wellord1(sK0,X7)),X7)
      | ~ r2_hidden(sK1(X6,k2_wellord1(sK0,X7)),X7)
      | k2_wellord1(sK0,X7) = X6
      | ~ r2_hidden(k4_tarski(sK1(X6,k2_wellord1(sK0,X7)),sK2(X6,k2_wellord1(sK0,X7))),X6)
      | ~ v1_relat_1(k2_wellord1(sK0,X7))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f120,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f120,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_wellord1(sK0,X6))
      | ~ r2_hidden(k4_tarski(X4,X5),sK0)
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X4,X6) ) ),
    inference(resolution,[],[f105,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t30_wellord1.p',t106_zfmisc_1)).

fof(f105,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k2_zfmisc_1(X4,X4))
      | r2_hidden(X5,k2_wellord1(sK0,X4))
      | ~ r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f97,f102])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
