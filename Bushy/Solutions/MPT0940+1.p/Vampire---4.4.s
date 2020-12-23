%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord2__t5_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 300 expanded)
%              Number of leaves         :    9 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  259 (1728 expanded)
%              Number of equality atoms :   46 ( 313 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(global_subsumption,[],[f159,f172])).

fof(f172,plain,(
    ~ r1_tarski(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0)) ),
    inference(unit_resulting_resolution,[],[f126,f149,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',d10_xboole_0)).

fof(f149,plain,(
    r1_tarski(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)) ),
    inference(unit_resulting_resolution,[],[f117,f118,f127,f102])).

fof(f102,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | r1_tarski(X4,X5)
      | ~ r2_hidden(X4,X0) ) ),
    inference(global_subsumption,[],[f65,f97])).

fof(f97,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',d1_wellord2)).

fof(f65,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',dt_k1_wellord2)).

fof(f127,plain,(
    r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),sK2(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f112,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ( sK1(X0,X1) != sK2(X0,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK1(X0,X1) != sK2(X0,X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( X2 = X3
                | ~ r2_hidden(k4_tarski(X3,X2),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',d4_relat_2)).

fof(f112,plain,(
    ~ r4_relat_2(k1_wellord2(sK0),sK0) ),
    inference(forward_demodulation,[],[f110,f103])).

fof(f103,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f65,f98])).

fof(f98,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,(
    ~ r4_relat_2(k1_wellord2(sK0),k3_relat_1(k1_wellord2(sK0))) ),
    inference(unit_resulting_resolution,[],[f65,f62,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r4_relat_2(X0,k3_relat_1(X0))
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',d12_relat_2)).

fof(f62,plain,(
    ~ v4_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ~ v4_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f45])).

fof(f45,plain,
    ( ? [X0] : ~ v4_relat_2(k1_wellord2(X0))
   => ~ v4_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] : ~ v4_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t5_wellord2.p',t5_wellord2)).

fof(f118,plain,(
    r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f112,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f117,plain,(
    r2_hidden(sK1(k1_wellord2(sK0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f112,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f126,plain,(
    sK1(k1_wellord2(sK0),sK0) != sK2(k1_wellord2(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f112,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != sK2(X0,X1)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f159,plain,(
    r1_tarski(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0)) ),
    inference(unit_resulting_resolution,[],[f118,f117,f134,f102])).

fof(f134,plain,(
    r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK1(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f112,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r4_relat_2(X0,X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
