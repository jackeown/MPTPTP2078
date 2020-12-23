%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t24_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:12 EDT 2019

% Result     : Theorem 14.61s
% Output     : Refutation 14.61s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 279 expanded)
%              Number of leaves         :    9 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  231 (1217 expanded)
%              Number of equality atoms :   16 (  70 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7306,plain,(
    $false ),
    inference(global_subsumption,[],[f2351,f7263])).

fof(f7263,plain,(
    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f3783,f7036,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',t106_zfmisc_1)).

fof(f7036,plain,(
    r2_hidden(sK4(k2_wellord1(sK1,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f525,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f525,plain,(
    r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f90,f103])).

fof(f103,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X12,k2_wellord1(sK1,X11))
      | r2_hidden(X12,k2_zfmisc_1(X11,X11)) ) ),
    inference(superposition,[],[f83,f86])).

fof(f86,plain,(
    ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',d6_wellord1)).

fof(f53,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ v8_relat_2(k2_wellord1(sK1,sK0))
    & v8_relat_2(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ~ v8_relat_2(k2_wellord1(X1,X0))
        & v8_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v8_relat_2(k2_wellord1(sK1,sK0))
      & v8_relat_2(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ v8_relat_2(k2_wellord1(X1,X0))
      & v8_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ v8_relat_2(k2_wellord1(X1,X0))
      & v8_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v8_relat_2(X1)
         => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',t24_wellord1)).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',d4_xboole_0)).

fof(f90,plain,(
    r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f85,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',l2_wellord1)).

fof(f85,plain,(
    ! [X0] : v1_relat_1(k2_wellord1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f53,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t24_wellord1.p',dt_k2_wellord1)).

fof(f55,plain,(
    ~ v8_relat_2(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f3783,plain,(
    r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f122,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,(
    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f89,f103])).

fof(f89,plain,(
    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f85,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2351,plain,(
    ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_zfmisc_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f91,f2286,f102])).

fof(f102,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X10,k2_zfmisc_1(X9,X9))
      | r2_hidden(X10,k2_wellord1(sK1,X9))
      | ~ r2_hidden(X10,sK1) ) ),
    inference(superposition,[],[f82,f86])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2286,plain,(
    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f53,f54,f123,f526,f58])).

fof(f58,plain,(
    ! [X6,X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f526,plain,(
    r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f90,f104])).

fof(f104,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(X14,k2_wellord1(sK1,X13))
      | r2_hidden(X14,sK1) ) ),
    inference(superposition,[],[f84,f86])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f123,plain,(
    r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f89,f104])).

fof(f54,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK4(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f85,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0),sK4(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
