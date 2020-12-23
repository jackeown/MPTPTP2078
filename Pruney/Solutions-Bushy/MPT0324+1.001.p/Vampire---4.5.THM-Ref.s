%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0324+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:45 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 (  44 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :  124 ( 172 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f14,f15,f52,f24])).

fof(f24,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f11,f12])).

fof(f12,plain,(
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

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f52,plain,(
    ~ r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : sQ6_eqProxy(k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(equality_proxy_replacement,[],[f23,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f49,plain,(
    ! [X2] :
      ( ~ sQ6_eqProxy(k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)),X2)
      | ~ r2_hidden(sK0,X2) ) ),
    inference(resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sQ6_eqProxy(X1,X0)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( ~ sQ6_eqProxy(X0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
      | ~ r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f41,f36])).

fof(f36,plain,(
    ! [X0] : sQ6_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ sQ6_eqProxy(X1,sK0)
      | ~ r2_hidden(X1,X0)
      | ~ sQ6_eqProxy(X0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ) ),
    inference(resolution,[],[f35,f16])).

fof(f16,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
    & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
        & r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
      & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ sQ6_eqProxy(X2,X3)
      | ~ r2_hidden(X0,X2)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f27])).

fof(f15,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
