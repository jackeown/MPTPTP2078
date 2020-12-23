%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t15_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:04 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 235 expanded)
%              Number of equality atoms :   74 ( 112 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f71,f90,f121])).

fof(f121,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f96,f82])).

fof(f82,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f32,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t15_mcart_1.p',t10_mcart_1)).

fof(f32,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
      | ( k1_mcart_1(sK0) != sK2
        & k1_mcart_1(sK0) != sK1 ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
        | ( k1_mcart_1(sK0) != sK2
          & k1_mcart_1(sK0) != sK1 ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t15_mcart_1.p',t15_mcart_1)).

fof(f96,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f70,f57,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t15_mcart_1.p',d2_tarski)).

fof(f57,plain,
    ( k1_mcart_1(sK0) != sK1
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_1
  <=> k1_mcart_1(sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f70,plain,
    ( k1_mcart_1(sK0) != sK2
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_5
  <=> k1_mcart_1(sK0) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f90,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f86,f63])).

fof(f63,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_3
  <=> ~ r2_hidden(k2_mcart_1(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f86,plain,(
    r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(unit_resulting_resolution,[],[f32,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,
    ( ~ spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f34,f62,f69])).

fof(f34,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | k1_mcart_1(sK0) != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f33,f62,f56])).

fof(f33,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | k1_mcart_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
