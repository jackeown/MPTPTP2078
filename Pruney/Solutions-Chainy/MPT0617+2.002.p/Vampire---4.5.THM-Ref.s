%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:45 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 614 expanded)
%              Number of leaves         :   10 ( 197 expanded)
%              Depth                    :   23
%              Number of atoms          :  300 (4463 expanded)
%              Number of equality atoms :   71 (1469 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(subsumption_resolution,[],[f284,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)
        | ~ r2_hidden(X2,k1_relat_1(sK0)) )
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) )
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & ! [X2] :
              ( k1_funct_1(X1,X2) = k1_funct_1(sK0,X2)
              | ~ r2_hidden(X2,k1_relat_1(sK0)) )
          & k1_relat_1(X1) = k1_relat_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( sK0 != X1
        & ! [X2] :
            ( k1_funct_1(X1,X2) = k1_funct_1(sK0,X2)
            | ~ r2_hidden(X2,k1_relat_1(sK0)) )
        & k1_relat_1(X1) = k1_relat_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & ! [X2] :
          ( k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)
          | ~ r2_hidden(X2,k1_relat_1(sK0)) )
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2] :
                    ( r2_hidden(X2,k1_relat_1(X0))
                   => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f284,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f283,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f283,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f282,f32])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f282,plain,
    ( sK0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f279,f272])).

fof(f272,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    inference(backward_demodulation,[],[f241,f270])).

fof(f270,plain,(
    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f269,f26])).

fof(f269,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f265,f27])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f265,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f242,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f242,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) ),
    inference(backward_demodulation,[],[f233,f238])).

fof(f238,plain,(
    k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(sK0,sK2(sK0,sK1)) ),
    inference(resolution,[],[f235,f31])).

fof(f31,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f235,plain,(
    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f234,f46])).

fof(f46,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f234,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f231,f30])).

fof(f30,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

% (7857)Refutation not found, incomplete strategy% (7857)------------------------------
% (7857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f231,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f229,f46])).

% (7857)Termination reason: Refutation not found, incomplete strategy

fof(f229,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f227,f32])).

% (7857)Memory used [KB]: 1663
% (7857)Time elapsed: 0.103 s
% (7857)------------------------------
% (7857)------------------------------
fof(f227,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f118,f28])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0)
      | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f35,f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(f233,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f232,f28])).

fof(f232,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f230,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f230,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)
    | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f229,f42])).

fof(f241,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK1) ),
    inference(backward_demodulation,[],[f236,f238])).

fof(f236,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK1,sK2(sK0,sK1))),sK1) ),
    inference(resolution,[],[f235,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f50,f29])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f48,f30])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f279,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | sK0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f273,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | X0 = X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f273,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) ),
    inference(backward_demodulation,[],[f244,f270])).

fof(f244,plain,(
    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f243,f26])).

fof(f243,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f239,f27])).

fof(f239,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f235,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (7859)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.49  % (7865)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (7860)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (7858)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (7862)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (7854)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.18/0.51  % (7874)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.18/0.51  % (7853)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.18/0.51  % (7852)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.18/0.52  % (7867)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.18/0.52  % (7857)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.18/0.52  % (7853)Refutation found. Thanks to Tanya!
% 1.18/0.52  % SZS status Theorem for theBenchmark
% 1.18/0.52  % SZS output start Proof for theBenchmark
% 1.18/0.52  fof(f285,plain,(
% 1.18/0.52    $false),
% 1.18/0.52    inference(subsumption_resolution,[],[f284,f26])).
% 1.18/0.52  fof(f26,plain,(
% 1.18/0.52    v1_relat_1(sK0)),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  fof(f13,plain,(
% 1.18/0.52    (sK0 != sK1 & ! [X2] : (k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).
% 1.18/0.52  fof(f11,plain,(
% 1.18/0.52    ? [X0] : (? [X1] : (X0 != X1 & ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (sK0 != X1 & ! [X2] : (k1_funct_1(X1,X2) = k1_funct_1(sK0,X2) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k1_relat_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f12,plain,(
% 1.18/0.52    ? [X1] : (sK0 != X1 & ! [X2] : (k1_funct_1(X1,X2) = k1_funct_1(sK0,X2) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(X1) = k1_relat_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != sK1 & ! [X2] : (k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) | ~r2_hidden(X2,k1_relat_1(sK0))) & k1_relat_1(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f7,plain,(
% 1.18/0.52    ? [X0] : (? [X1] : (X0 != X1 & ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.18/0.52    inference(flattening,[],[f6])).
% 1.18/0.52  fof(f6,plain,(
% 1.18/0.52    ? [X0] : (? [X1] : ((X0 != X1 & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.18/0.52    inference(ennf_transformation,[],[f5])).
% 1.18/0.52  fof(f5,negated_conjecture,(
% 1.18/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.18/0.52    inference(negated_conjecture,[],[f4])).
% 1.18/0.52  fof(f4,conjecture,(
% 1.18/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.18/0.52  fof(f284,plain,(
% 1.18/0.52    ~v1_relat_1(sK0)),
% 1.18/0.52    inference(subsumption_resolution,[],[f283,f28])).
% 1.18/0.52  fof(f28,plain,(
% 1.18/0.52    v1_relat_1(sK1)),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  fof(f283,plain,(
% 1.18/0.52    ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 1.18/0.52    inference(subsumption_resolution,[],[f282,f32])).
% 1.18/0.52  fof(f32,plain,(
% 1.18/0.52    sK0 != sK1),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  fof(f282,plain,(
% 1.18/0.52    sK0 = sK1 | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 1.18/0.52    inference(subsumption_resolution,[],[f279,f272])).
% 1.18/0.52  fof(f272,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)),
% 1.18/0.52    inference(backward_demodulation,[],[f241,f270])).
% 1.18/0.52  fof(f270,plain,(
% 1.18/0.52    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))),
% 1.18/0.52    inference(subsumption_resolution,[],[f269,f26])).
% 1.18/0.52  fof(f269,plain,(
% 1.18/0.52    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) | ~v1_relat_1(sK0)),
% 1.18/0.52    inference(subsumption_resolution,[],[f265,f27])).
% 1.18/0.52  fof(f27,plain,(
% 1.18/0.52    v1_funct_1(sK0)),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  fof(f265,plain,(
% 1.18/0.52    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.18/0.52    inference(duplicate_literal_removal,[],[f263])).
% 1.18/0.52  fof(f263,plain,(
% 1.18/0.52    sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) | sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.18/0.52    inference(resolution,[],[f242,f42])).
% 1.18/0.52  fof(f42,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f25])).
% 1.18/0.52  fof(f25,plain,(
% 1.18/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.18/0.52    inference(flattening,[],[f24])).
% 1.18/0.52  fof(f24,plain,(
% 1.18/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.18/0.52    inference(nnf_transformation,[],[f10])).
% 1.18/0.52  fof(f10,plain,(
% 1.18/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.18/0.52    inference(flattening,[],[f9])).
% 1.18/0.52  fof(f9,plain,(
% 1.18/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.18/0.52    inference(ennf_transformation,[],[f3])).
% 1.18/0.52  fof(f3,axiom,(
% 1.18/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.18/0.52  fof(f242,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | sK3(sK0,sK1) = k1_funct_1(sK0,sK2(sK0,sK1))),
% 1.18/0.52    inference(backward_demodulation,[],[f233,f238])).
% 1.18/0.52  fof(f238,plain,(
% 1.18/0.52    k1_funct_1(sK1,sK2(sK0,sK1)) = k1_funct_1(sK0,sK2(sK0,sK1))),
% 1.18/0.52    inference(resolution,[],[f235,f31])).
% 1.18/0.52  fof(f31,plain,(
% 1.18/0.52    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK0)) | k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  fof(f235,plain,(
% 1.18/0.52    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))),
% 1.18/0.52    inference(subsumption_resolution,[],[f234,f46])).
% 1.18/0.52  fof(f46,plain,(
% 1.18/0.52    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.18/0.52    inference(equality_resolution,[],[f38])).
% 1.18/0.52  fof(f38,plain,(
% 1.18/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.18/0.52    inference(cnf_transformation,[],[f23])).
% 1.18/0.52  fof(f23,plain,(
% 1.18/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f22,f21,f20])).
% 1.18/0.52  fof(f20,plain,(
% 1.18/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f21,plain,(
% 1.18/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f22,plain,(
% 1.18/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f19,plain,(
% 1.18/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.18/0.52    inference(rectify,[],[f18])).
% 1.18/0.52  fof(f18,plain,(
% 1.18/0.52    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.18/0.52    inference(nnf_transformation,[],[f2])).
% 1.18/0.52  fof(f2,axiom,(
% 1.18/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.18/0.52  fof(f234,plain,(
% 1.18/0.52    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)),
% 1.18/0.52    inference(forward_demodulation,[],[f231,f30])).
% 1.18/0.52  fof(f30,plain,(
% 1.18/0.52    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  % (7857)Refutation not found, incomplete strategy% (7857)------------------------------
% 1.18/0.52  % (7857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  fof(f231,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))),
% 1.18/0.52    inference(resolution,[],[f229,f46])).
% 1.18/0.52  % (7857)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  fof(f229,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)),
% 1.18/0.52    inference(subsumption_resolution,[],[f227,f32])).
% 1.18/0.52  % (7857)Memory used [KB]: 1663
% 1.18/0.52  % (7857)Time elapsed: 0.103 s
% 1.18/0.52  % (7857)------------------------------
% 1.18/0.52  % (7857)------------------------------
% 1.18/0.52  fof(f227,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) | sK0 = sK1),
% 1.18/0.52    inference(resolution,[],[f118,f28])).
% 1.18/0.52  fof(f118,plain,(
% 1.18/0.52    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),sK0) | r2_hidden(k4_tarski(sK2(sK0,X0),sK3(sK0,X0)),X0) | sK0 = X0) )),
% 1.18/0.52    inference(resolution,[],[f35,f26])).
% 1.18/0.52  fof(f35,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~v1_relat_1(X1) | X0 = X1) )),
% 1.18/0.52    inference(cnf_transformation,[],[f17])).
% 1.18/0.52  fof(f17,plain,(
% 1.18/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ((~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f16])).
% 1.18/0.52  fof(f16,plain,(
% 1.18/0.52    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f15,plain,(
% 1.18/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.18/0.52    inference(rectify,[],[f14])).
% 1.18/0.52  fof(f14,plain,(
% 1.18/0.52    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.18/0.52    inference(nnf_transformation,[],[f8])).
% 1.18/0.52  fof(f8,plain,(
% 1.18/0.52    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.18/0.52    inference(ennf_transformation,[],[f1])).
% 1.18/0.52  fof(f1,axiom,(
% 1.18/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 1.18/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).
% 1.18/0.52  fof(f233,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1))),
% 1.18/0.52    inference(subsumption_resolution,[],[f232,f28])).
% 1.18/0.52  fof(f232,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_relat_1(sK1)),
% 1.18/0.52    inference(subsumption_resolution,[],[f230,f29])).
% 1.18/0.52  fof(f29,plain,(
% 1.18/0.52    v1_funct_1(sK1)),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  fof(f230,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0) | sK3(sK0,sK1) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.18/0.52    inference(resolution,[],[f229,f42])).
% 1.18/0.52  fof(f241,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK1)),
% 1.18/0.52    inference(backward_demodulation,[],[f236,f238])).
% 1.18/0.52  fof(f236,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK1,sK2(sK0,sK1))),sK1)),
% 1.18/0.52    inference(resolution,[],[f235,f52])).
% 1.18/0.52  fof(f52,plain,(
% 1.18/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)) )),
% 1.18/0.52    inference(subsumption_resolution,[],[f51,f28])).
% 1.18/0.52  fof(f51,plain,(
% 1.18/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) )),
% 1.18/0.52    inference(subsumption_resolution,[],[f50,f29])).
% 1.18/0.52  fof(f50,plain,(
% 1.18/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.18/0.52    inference(superposition,[],[f48,f30])).
% 1.18/0.52  fof(f48,plain,(
% 1.18/0.52    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.18/0.52    inference(equality_resolution,[],[f43])).
% 1.18/0.52  fof(f43,plain,(
% 1.18/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f25])).
% 1.18/0.52  fof(f279,plain,(
% 1.18/0.52    ~r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) | sK0 = sK1 | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 1.18/0.52    inference(resolution,[],[f273,f36])).
% 1.18/0.52  fof(f36,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | X0 = X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f17])).
% 1.18/0.52  fof(f273,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK0)),
% 1.18/0.52    inference(backward_demodulation,[],[f244,f270])).
% 1.18/0.52  fof(f244,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0)),
% 1.18/0.52    inference(subsumption_resolution,[],[f243,f26])).
% 1.18/0.52  fof(f243,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0) | ~v1_relat_1(sK0)),
% 1.18/0.52    inference(subsumption_resolution,[],[f239,f27])).
% 1.18/0.52  fof(f239,plain,(
% 1.18/0.52    r2_hidden(k4_tarski(sK2(sK0,sK1),k1_funct_1(sK0,sK2(sK0,sK1))),sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.18/0.52    inference(resolution,[],[f235,f48])).
% 1.18/0.52  % SZS output end Proof for theBenchmark
% 1.18/0.52  % (7853)------------------------------
% 1.18/0.52  % (7853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (7853)Termination reason: Refutation
% 1.18/0.52  
% 1.18/0.52  % (7853)Memory used [KB]: 6396
% 1.18/0.52  % (7853)Time elapsed: 0.112 s
% 1.18/0.52  % (7853)------------------------------
% 1.18/0.52  % (7853)------------------------------
% 1.18/0.52  % (7870)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.18/0.52  % (7849)Success in time 0.159 s
%------------------------------------------------------------------------------
