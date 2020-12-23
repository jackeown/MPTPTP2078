%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0502+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 22.75s
% Output     : Refutation 23.28s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 337 expanded)
%              Number of leaves         :   12 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  451 (1837 expanded)
%              Number of equality atoms :   36 ( 241 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16871,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4158,f6328,f6337,f7172,f15398,f16870])).

fof(f16870,plain,
    ( ~ spl151_3
    | ~ spl151_7
    | spl151_8
    | ~ spl151_9 ),
    inference(avatar_contradiction_clause,[],[f16869])).

fof(f16869,plain,
    ( $false
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8
    | ~ spl151_9 ),
    inference(subsumption_resolution,[],[f16868,f15445])).

fof(f15445,plain,
    ( r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK3)
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8 ),
    inference(subsumption_resolution,[],[f15438,f1718])).

fof(f1718,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1308])).

fof(f1308,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k7_relat_1(sK5,k3_xboole_0(sK3,sK4))
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f762,f1307])).

fof(f1307,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) != k7_relat_1(X2,k3_xboole_0(X0,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k7_relat_1(sK5,k3_xboole_0(sK3,sK4))
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f762,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) != k7_relat_1(X2,k3_xboole_0(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f675])).

fof(f675,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f674])).

fof(f674,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f15438,plain,
    ( r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8 ),
    inference(resolution,[],[f15433,f3980])).

fof(f3980,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2903,f2004])).

fof(f2004,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f871])).

fof(f871,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f656])).

fof(f656,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f2903,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1857])).

fof(f1857,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1342])).

fof(f1342,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK22(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
                    & r2_hidden(sK22(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23])],[f1340,f1341])).

fof(f1341,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
          | ~ r2_hidden(sK22(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
            & r2_hidden(sK22(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1340,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1339])).

fof(f1339,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1338])).

fof(f1338,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f833])).

fof(f833,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f641])).

fof(f641,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f15433,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8 ),
    inference(subsumption_resolution,[],[f15403,f6322])).

fof(f6322,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | spl151_8 ),
    inference(avatar_component_clause,[],[f6321])).

fof(f6321,plain,
    ( spl151_8
  <=> r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_8])])).

fof(f15403,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ spl151_3
    | ~ spl151_7 ),
    inference(subsumption_resolution,[],[f15402,f4139])).

fof(f4139,plain,
    ( v1_relat_1(k7_relat_1(sK5,sK3))
    | ~ spl151_3 ),
    inference(avatar_component_clause,[],[f4138])).

fof(f4138,plain,
    ( spl151_3
  <=> v1_relat_1(k7_relat_1(sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_3])])).

fof(f15402,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,sK3))
    | ~ spl151_7 ),
    inference(subsumption_resolution,[],[f3991,f6318])).

fof(f6318,plain,
    ( v1_relat_1(k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ spl151_7 ),
    inference(avatar_component_clause,[],[f6317])).

fof(f6317,plain,
    ( spl151_7
  <=> v1_relat_1(k7_relat_1(sK5,k3_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_7])])).

fof(f3991,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,sK3)) ),
    inference(resolution,[],[f3181,f3115])).

fof(f3115,plain,(
    ~ sQ150_eqProxy(k7_relat_1(k7_relat_1(sK5,sK3),sK4),k7_relat_1(sK5,k3_xboole_0(sK3,sK4))) ),
    inference(equality_proxy_replacement,[],[f1719,f3097])).

fof(f3097,plain,(
    ! [X1,X0] :
      ( sQ150_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ150_eqProxy])])).

fof(f1719,plain,(
    k7_relat_1(k7_relat_1(sK5,sK3),sK4) != k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f1308])).

fof(f3181,plain,(
    ! [X2,X0,X1] :
      ( sQ150_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1861,f3097])).

fof(f1861,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1342])).

fof(f16868,plain,
    ( ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK3)
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8
    | ~ spl151_9 ),
    inference(subsumption_resolution,[],[f16865,f6327])).

fof(f6327,plain,
    ( r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | ~ spl151_9 ),
    inference(avatar_component_clause,[],[f6325])).

fof(f6325,plain,
    ( spl151_9
  <=> r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl151_9])])).

fof(f16865,plain,
    ( ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK3)
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8 ),
    inference(resolution,[],[f16862,f2977])).

fof(f2977,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2530])).

fof(f2530,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1607])).

fof(f1607,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK123(X0,X1,X2),X1)
            | ~ r2_hidden(sK123(X0,X1,X2),X0)
            | ~ r2_hidden(sK123(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK123(X0,X1,X2),X1)
              & r2_hidden(sK123(X0,X1,X2),X0) )
            | r2_hidden(sK123(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK123])],[f1605,f1606])).

fof(f1606,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK123(X0,X1,X2),X1)
          | ~ r2_hidden(sK123(X0,X1,X2),X0)
          | ~ r2_hidden(sK123(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK123(X0,X1,X2),X1)
            & r2_hidden(sK123(X0,X1,X2),X0) )
          | r2_hidden(sK123(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1605,plain,(
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
    inference(rectify,[],[f1604])).

fof(f1604,plain,(
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
    inference(flattening,[],[f1603])).

fof(f1603,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f16862,plain,
    ( ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8 ),
    inference(subsumption_resolution,[],[f15406,f15444])).

fof(f15444,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),sK5)
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8 ),
    inference(subsumption_resolution,[],[f15437,f1718])).

fof(f15437,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl151_3
    | ~ spl151_7
    | spl151_8 ),
    inference(resolution,[],[f15433,f3983])).

fof(f3983,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2902,f2004])).

fof(f2902,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1858])).

fof(f1858,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1342])).

fof(f15406,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),sK5)
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | spl151_8 ),
    inference(subsumption_resolution,[],[f15405,f1718])).

fof(f15405,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),sK5)
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | ~ v1_relat_1(sK5)
    | spl151_8 ),
    inference(resolution,[],[f6322,f3984])).

fof(f3984,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f2901,f2004])).

fof(f2901,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1859])).

fof(f1859,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1342])).

fof(f15398,plain,
    ( ~ spl151_3
    | ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(avatar_contradiction_clause,[],[f15396])).

fof(f15396,plain,
    ( $false
    | ~ spl151_3
    | ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(unit_resulting_resolution,[],[f6366,f15379,f2979])).

fof(f2979,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f2528])).

fof(f2528,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1607])).

fof(f15379,plain,
    ( ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK3)
    | ~ spl151_3
    | ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(subsumption_resolution,[],[f7210,f6365])).

fof(f6365,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),sK5)
    | ~ spl151_8 ),
    inference(subsumption_resolution,[],[f6358,f1718])).

fof(f6358,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl151_8 ),
    inference(resolution,[],[f6323,f3983])).

fof(f6323,plain,
    ( r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ spl151_8 ),
    inference(avatar_component_clause,[],[f6321])).

fof(f7210,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),sK5)
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK3)
    | ~ spl151_3
    | ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(subsumption_resolution,[],[f7209,f1718])).

fof(f7209,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),sK5)
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK3)
    | ~ v1_relat_1(sK5)
    | ~ spl151_3
    | ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(resolution,[],[f7205,f3984])).

fof(f7205,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | ~ spl151_3
    | ~ spl151_7
    | ~ spl151_8
    | ~ spl151_9 ),
    inference(subsumption_resolution,[],[f7175,f6327])).

fof(f7175,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | ~ spl151_3
    | ~ spl151_7
    | ~ spl151_8 ),
    inference(subsumption_resolution,[],[f7174,f4139])).

fof(f7174,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | ~ v1_relat_1(k7_relat_1(sK5,sK3))
    | ~ spl151_7
    | ~ spl151_8 ),
    inference(subsumption_resolution,[],[f7173,f6318])).

fof(f7173,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | ~ v1_relat_1(k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,sK3))
    | ~ spl151_8 ),
    inference(subsumption_resolution,[],[f3992,f6323])).

fof(f3992,plain,
    ( ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,sK3))
    | ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | ~ r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,sK3)) ),
    inference(resolution,[],[f3180,f3115])).

fof(f3180,plain,(
    ! [X2,X0,X1] :
      ( sQ150_eqProxy(k7_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
      | ~ r2_hidden(sK22(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1862,f3097])).

fof(f1862,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X0)
      | ~ r2_hidden(sK22(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1342])).

fof(f6366,plain,
    ( r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | ~ spl151_8 ),
    inference(subsumption_resolution,[],[f6359,f1718])).

fof(f6359,plain,
    ( r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),k3_xboole_0(sK3,sK4))
    | ~ v1_relat_1(sK5)
    | ~ spl151_8 ),
    inference(resolution,[],[f6323,f3980])).

fof(f7172,plain,
    ( ~ spl151_8
    | spl151_9 ),
    inference(avatar_contradiction_clause,[],[f7171])).

fof(f7171,plain,
    ( $false
    | ~ spl151_8
    | spl151_9 ),
    inference(subsumption_resolution,[],[f7166,f6326])).

fof(f6326,plain,
    ( ~ r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | spl151_9 ),
    inference(avatar_component_clause,[],[f6325])).

fof(f7166,plain,
    ( r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | ~ spl151_8 ),
    inference(resolution,[],[f6366,f2978])).

fof(f2978,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f2529])).

fof(f2529,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1607])).

fof(f6337,plain,(
    spl151_7 ),
    inference(avatar_contradiction_clause,[],[f6336])).

fof(f6336,plain,
    ( $false
    | spl151_7 ),
    inference(subsumption_resolution,[],[f6330,f1718])).

fof(f6330,plain,
    ( ~ v1_relat_1(sK5)
    | spl151_7 ),
    inference(resolution,[],[f6319,f2004])).

fof(f6319,plain,
    ( ~ v1_relat_1(k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | spl151_7 ),
    inference(avatar_component_clause,[],[f6317])).

fof(f6328,plain,
    ( ~ spl151_7
    | spl151_8
    | spl151_9
    | ~ spl151_3 ),
    inference(avatar_split_clause,[],[f6312,f4138,f6325,f6321,f6317])).

fof(f6312,plain,
    ( r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ spl151_3 ),
    inference(subsumption_resolution,[],[f3990,f4139])).

fof(f3990,plain,
    ( r2_hidden(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK4)
    | r2_hidden(k4_tarski(sK22(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4))),sK23(k7_relat_1(sK5,sK3),sK4,k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))),k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,k3_xboole_0(sK3,sK4)))
    | ~ v1_relat_1(k7_relat_1(sK5,sK3)) ),
    inference(resolution,[],[f3182,f3115])).

fof(f3182,plain,(
    ! [X2,X0,X1] :
      ( sQ150_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(sK22(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f1860,f3097])).

fof(f1860,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK22(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK22(X0,X1,X2),sK23(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1342])).

fof(f4158,plain,(
    spl151_3 ),
    inference(avatar_contradiction_clause,[],[f4157])).

fof(f4157,plain,
    ( $false
    | spl151_3 ),
    inference(subsumption_resolution,[],[f4152,f1718])).

fof(f4152,plain,
    ( ~ v1_relat_1(sK5)
    | spl151_3 ),
    inference(resolution,[],[f4140,f2004])).

fof(f4140,plain,
    ( ~ v1_relat_1(k7_relat_1(sK5,sK3))
    | spl151_3 ),
    inference(avatar_component_clause,[],[f4138])).
%------------------------------------------------------------------------------
