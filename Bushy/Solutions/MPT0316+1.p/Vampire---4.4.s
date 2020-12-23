%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t128_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:59 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  88 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  184 ( 351 expanded)
%              Number of equality atoms :   51 ( 105 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f70,f99,f115,f148])).

fof(f148,plain,
    ( ~ spl5_0
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f49,f120,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t128_zfmisc_1.p',l54_zfmisc_1)).

fof(f120,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t128_zfmisc_1.p',d1_tarski)).

fof(f52,plain,
    ( sK0 != sK2
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_3
  <=> sK0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f49,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_0
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f115,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f104,f60])).

fof(f60,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_5
  <=> ~ r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f104,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f69,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_6
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f99,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f63,f72,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f71,f55])).

fof(f55,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f71,plain,
    ( sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f42,f63])).

fof(f42,plain,
    ( ~ r2_hidden(sK1,sK3)
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) ),
    inference(inner_rewriting,[],[f30])).

fof(f30,plain,
    ( ~ r2_hidden(sK1,sK3)
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r2_hidden(sK1,sK3)
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
    & ( ( r2_hidden(sK1,sK3)
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK1,sK3)
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
      & ( ( r2_hidden(sK1,sK3)
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t128_zfmisc_1.p',t128_zfmisc_1)).

fof(f63,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_4
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f70,plain,
    ( spl5_4
    | spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f54,f68,f62])).

fof(f57,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | r2_hidden(sK1,sK3)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f29,f55])).

fof(f29,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,
    ( spl5_0
    | spl5_2 ),
    inference(avatar_split_clause,[],[f28,f54,f48])).

fof(f28,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
