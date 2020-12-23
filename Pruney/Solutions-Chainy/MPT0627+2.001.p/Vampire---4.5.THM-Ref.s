%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 370 expanded)
%              Number of leaves         :   10 ( 105 expanded)
%              Depth                    :   34
%              Number of atoms          :  488 (2280 expanded)
%              Number of equality atoms :   39 ( 324 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(subsumption_resolution,[],[f279,f29])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0))
    & r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0))
            & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(X2,sK0))
          & r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( k1_funct_1(k5_relat_1(X2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(X2,sK0))
        & r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0))
      & r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0))
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0))
          & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
             => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f279,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f278,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f278,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f277,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f277,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f276,f28])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f276,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f275,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f275,plain,(
    ~ v1_funct_1(k5_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f274,f31])).

fof(f31,plain,(
    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f274,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f273,f30])).

fof(f273,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f272,f28])).

fof(f272,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f271,f27])).

fof(f271,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f266,f29])).

fof(f266,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f264,f158])).

fof(f158,plain,(
    ! [X12,X10,X11] :
      ( r2_hidden(k1_funct_1(X11,X12),k1_relat_1(X10))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_1(X11)
      | ~ r2_hidden(X12,k1_relat_1(k5_relat_1(X11,X10))) ) ),
    inference(subsumption_resolution,[],[f157,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f157,plain,(
    ! [X12,X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | r2_hidden(k1_funct_1(X11,X12),k1_relat_1(X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_1(X11)
      | ~ r2_hidden(X12,k1_relat_1(k5_relat_1(X11,X10)))
      | ~ v1_relat_1(k5_relat_1(X11,X10)) ) ),
    inference(subsumption_resolution,[],[f148,f40])).

fof(f148,plain,(
    ! [X12,X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | r2_hidden(k1_funct_1(X11,X12),k1_relat_1(X10))
      | ~ v1_funct_1(X10)
      | ~ v1_funct_1(X11)
      | ~ r2_hidden(X12,k1_relat_1(k5_relat_1(X11,X10)))
      | ~ v1_funct_1(k5_relat_1(X11,X10))
      | ~ v1_relat_1(k5_relat_1(X11,X10)) ) ),
    inference(resolution,[],[f121,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

% (9368)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f121,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(X12,X13))
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(X12)
      | r2_hidden(k1_funct_1(X12,X14),k1_relat_1(X13))
      | ~ v1_funct_1(X13)
      | ~ v1_funct_1(X12) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X14,X12,X15,X13] :
      ( r2_hidden(k1_funct_1(X12,X14),k1_relat_1(X13))
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(X12)
      | ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(X12,X13))
      | ~ v1_funct_1(X13)
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(X12)
      | ~ r2_hidden(k4_tarski(X14,X15),k5_relat_1(X12,X13))
      | ~ v1_funct_1(X12) ) ),
    inference(superposition,[],[f58,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (9360)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f58,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK6(X6,X7,X4,X5),k1_relat_1(X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f55,f41])).

fof(f55,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | r2_hidden(sK6(X6,X7,X4,X5),k1_relat_1(X7))
      | ~ v1_funct_1(X7) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | r2_hidden(sK6(X6,X7,X4,X5),k1_relat_1(X7))
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f264,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(k5_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f263,f29])).

fof(f263,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f262,f30])).

fof(f262,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f259,f106])).

fof(f106,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f105,f29])).

fof(f105,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f104,f30])).

fof(f104,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f103,f27])).

fof(f103,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f102,f28])).

fof(f102,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f99,f40])).

fof(f99,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f98,f27])).

fof(f98,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f97,f30])).

fof(f97,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f90,f29])).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f76,f31])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X1)
      | r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k5_relat_1(X1,X0)) ) ),
    inference(subsumption_resolution,[],[f72,f41])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f71,f48])).

fof(f71,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | r2_hidden(X4,k1_relat_1(X6))
      | ~ v1_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f68,f41])).

fof(f68,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | r2_hidden(X4,k1_relat_1(X6))
      | ~ v1_funct_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | r2_hidden(X4,k1_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f47,f42])).

fof(f259,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f241,f48])).

fof(f241,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f240,f27])).

fof(f240,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f233,f28])).

fof(f233,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f231,f48])).

fof(f231,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1)
      | ~ r2_hidden(k4_tarski(sK0,X0),sK2)
      | ~ v1_funct_1(k5_relat_1(sK2,sK1)) ) ),
    inference(equality_resolution,[],[f226])).

fof(f226,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1,k1_funct_1(sK2,sK0)) != X0
      | ~ r2_hidden(k4_tarski(sK0,X1),sK2)
      | ~ r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ v1_funct_1(k5_relat_1(sK2,sK1)) ) ),
    inference(subsumption_resolution,[],[f225,f29])).

fof(f225,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1,k1_funct_1(sK2,sK0)) != X0
      | ~ r2_hidden(k4_tarski(sK0,X1),sK2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ v1_funct_1(k5_relat_1(sK2,sK1)) ) ),
    inference(subsumption_resolution,[],[f207,f27])).

fof(f207,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1,k1_funct_1(sK2,sK0)) != X0
      | ~ r2_hidden(k4_tarski(sK0,X1),sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ v1_funct_1(k5_relat_1(sK2,sK1)) ) ),
    inference(superposition,[],[f32,f88])).

fof(f88,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( k1_funct_1(k5_relat_1(X9,X7),X8) = X6
      | ~ r2_hidden(k4_tarski(X8,X5),X9)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X9)
      | ~ r2_hidden(k4_tarski(X5,X6),X7)
      | ~ v1_funct_1(k5_relat_1(X9,X7)) ) ),
    inference(subsumption_resolution,[],[f86,f41])).

fof(f86,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X7)
      | ~ r2_hidden(k4_tarski(X8,X5),X9)
      | ~ v1_relat_1(k5_relat_1(X9,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X9)
      | k1_funct_1(k5_relat_1(X9,X7),X8) = X6
      | ~ v1_funct_1(k5_relat_1(X9,X7)) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X7)
      | ~ r2_hidden(k4_tarski(X8,X5),X9)
      | ~ v1_relat_1(k5_relat_1(X9,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X9)
      | k1_funct_1(k5_relat_1(X9,X7),X8) = X6
      | ~ v1_funct_1(k5_relat_1(X9,X7))
      | ~ v1_relat_1(k5_relat_1(X9,X7)) ) ),
    inference(resolution,[],[f45,f43])).

fof(f45,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:38:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.46  % (9356)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (9371)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (9363)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (9371)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f279,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    (k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0)) & r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0)) & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k1_funct_1(k5_relat_1(X2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(X2,sK0)) & r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X2] : (k1_funct_1(k5_relat_1(X2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(X2,sK0)) & r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0)) & r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0)) & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) != k1_funct_1(X1,k1_funct_1(X2,X0)) & r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f278,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f277,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f277,plain,(
% 0.20/0.50    ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f276,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    v1_funct_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f275,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f274,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f273,f30])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f272,f28])).
% 0.20/0.50  fof(f272,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f271,f27])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f266,f29])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.20/0.50    inference(resolution,[],[f264,f158])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    ( ! [X12,X10,X11] : (r2_hidden(k1_funct_1(X11,X12),k1_relat_1(X10)) | ~v1_relat_1(X11) | ~v1_relat_1(X10) | ~v1_funct_1(X10) | ~v1_funct_1(X11) | ~r2_hidden(X12,k1_relat_1(k5_relat_1(X11,X10)))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f157,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ( ! [X12,X10,X11] : (~v1_relat_1(X10) | ~v1_relat_1(X11) | r2_hidden(k1_funct_1(X11,X12),k1_relat_1(X10)) | ~v1_funct_1(X10) | ~v1_funct_1(X11) | ~r2_hidden(X12,k1_relat_1(k5_relat_1(X11,X10))) | ~v1_relat_1(k5_relat_1(X11,X10))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f148,f40])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X12,X10,X11] : (~v1_relat_1(X10) | ~v1_relat_1(X11) | r2_hidden(k1_funct_1(X11,X12),k1_relat_1(X10)) | ~v1_funct_1(X10) | ~v1_funct_1(X11) | ~r2_hidden(X12,k1_relat_1(k5_relat_1(X11,X10))) | ~v1_funct_1(k5_relat_1(X11,X10)) | ~v1_relat_1(k5_relat_1(X11,X10))) )),
% 0.20/0.50    inference(resolution,[],[f121,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(equality_resolution,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  % (9368)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(nnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X14,X12,X15,X13] : (~r2_hidden(k4_tarski(X14,X15),k5_relat_1(X12,X13)) | ~v1_relat_1(X13) | ~v1_relat_1(X12) | r2_hidden(k1_funct_1(X12,X14),k1_relat_1(X13)) | ~v1_funct_1(X13) | ~v1_funct_1(X12)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ( ! [X14,X12,X15,X13] : (r2_hidden(k1_funct_1(X12,X14),k1_relat_1(X13)) | ~v1_relat_1(X13) | ~v1_relat_1(X12) | ~r2_hidden(k4_tarski(X14,X15),k5_relat_1(X12,X13)) | ~v1_funct_1(X13) | ~v1_relat_1(X13) | ~v1_relat_1(X12) | ~r2_hidden(k4_tarski(X14,X15),k5_relat_1(X12,X13)) | ~v1_funct_1(X12)) )),
% 0.20/0.50    inference(superposition,[],[f58,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f69,f41])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~v1_relat_1(k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3)) | ~v1_relat_1(k5_relat_1(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(resolution,[],[f47,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  % (9360)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(rectify,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X6,X4,X7,X5] : (r2_hidden(sK6(X6,X7,X4,X5),k1_relat_1(X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | ~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_funct_1(X7)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f55,f41])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X6,X4,X7,X5] : (~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | r2_hidden(sK6(X6,X7,X4,X5),k1_relat_1(X7)) | ~v1_funct_1(X7)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X6,X4,X7,X5] : (~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | r2_hidden(sK6(X6,X7,X4,X5),k1_relat_1(X7)) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) )),
% 0.20/0.50    inference(resolution,[],[f46,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~v1_funct_1(k5_relat_1(sK2,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f263,f29])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f262,f30])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f259,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f29])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f104,f30])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f103,f27])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f102,f28])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f99,f40])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f98,f27])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f97,f30])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f90,f29])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))),
% 0.20/0.50    inference(resolution,[],[f76,f31])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X0))) | ~v1_relat_1(X1) | r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(k5_relat_1(X1,X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f72,f41])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X0))) | ~v1_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(k5_relat_1(X1,X0))) )),
% 0.20/0.50    inference(resolution,[],[f71,f48])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X6,X4,X7,X5] : (~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | r2_hidden(X4,k1_relat_1(X6)) | ~v1_funct_1(X6)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f68,f41])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X6,X4,X7,X5] : (~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | r2_hidden(X4,k1_relat_1(X6)) | ~v1_funct_1(X6)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X6,X4,X7,X5] : (~r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | r2_hidden(X4,k1_relat_1(X6)) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) )),
% 0.20/0.50    inference(resolution,[],[f47,f42])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f241,f48])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))),
% 0.20/0.50    inference(subsumption_resolution,[],[f240,f27])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(subsumption_resolution,[],[f233,f28])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~v1_funct_1(k5_relat_1(sK2,sK1)) | ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.20/0.50    inference(resolution,[],[f231,f48])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k1_funct_1(sK1,k1_funct_1(sK2,sK0))),sK1) | ~r2_hidden(k4_tarski(sK0,X0),sK2) | ~v1_funct_1(k5_relat_1(sK2,sK1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f226])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_funct_1(sK1,k1_funct_1(sK2,sK0)) != X0 | ~r2_hidden(k4_tarski(sK0,X1),sK2) | ~r2_hidden(k4_tarski(X1,X0),sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f225,f29])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_funct_1(sK1,k1_funct_1(sK2,sK0)) != X0 | ~r2_hidden(k4_tarski(sK0,X1),sK2) | ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X1,X0),sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f207,f27])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_funct_1(sK1,k1_funct_1(sK2,sK0)) != X0 | ~r2_hidden(k4_tarski(sK0,X1),sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(X1,X0),sK1) | ~v1_funct_1(k5_relat_1(sK2,sK1))) )),
% 0.20/0.50    inference(superposition,[],[f32,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X6,X8,X7,X5,X9] : (k1_funct_1(k5_relat_1(X9,X7),X8) = X6 | ~r2_hidden(k4_tarski(X8,X5),X9) | ~v1_relat_1(X7) | ~v1_relat_1(X9) | ~r2_hidden(k4_tarski(X5,X6),X7) | ~v1_funct_1(k5_relat_1(X9,X7))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f86,f41])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X6,X8,X7,X5,X9] : (~r2_hidden(k4_tarski(X5,X6),X7) | ~r2_hidden(k4_tarski(X8,X5),X9) | ~v1_relat_1(k5_relat_1(X9,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X9) | k1_funct_1(k5_relat_1(X9,X7),X8) = X6 | ~v1_funct_1(k5_relat_1(X9,X7))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X6,X8,X7,X5,X9] : (~r2_hidden(k4_tarski(X5,X6),X7) | ~r2_hidden(k4_tarski(X8,X5),X9) | ~v1_relat_1(k5_relat_1(X9,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X9) | k1_funct_1(k5_relat_1(X9,X7),X8) = X6 | ~v1_funct_1(k5_relat_1(X9,X7)) | ~v1_relat_1(k5_relat_1(X9,X7))) )),
% 0.20/0.50    inference(resolution,[],[f45,f43])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X2,X0,X8,X7,X1,X9] : (r2_hidden(k4_tarski(X7,X8),X2) | ~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    k1_funct_1(k5_relat_1(sK2,sK1),sK0) != k1_funct_1(sK1,k1_funct_1(sK2,sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (9371)------------------------------
% 0.20/0.50  % (9371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9371)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (9371)Memory used [KB]: 1918
% 0.20/0.50  % (9371)Time elapsed: 0.087 s
% 0.20/0.50  % (9371)------------------------------
% 0.20/0.50  % (9371)------------------------------
% 0.20/0.50  % (9362)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (9355)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (9345)Success in time 0.154 s
%------------------------------------------------------------------------------
