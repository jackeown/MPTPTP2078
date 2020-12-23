%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0629+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:41 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   26 (  47 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 253 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4917,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4916,f2192])).

fof(f2192,plain,(
    ~ r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f1697])).

fof(f1697,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK4))
    & r2_hidden(sK3,k2_relat_1(k5_relat_1(sK5,sK4)))
    & v1_funct_1(sK5)
    & v1_relat_1(sK5)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f933,f1696,f1695])).

fof(f1695,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X0,k2_relat_1(X1))
            & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(sK3,k2_relat_1(sK4))
          & r2_hidden(sK3,k2_relat_1(k5_relat_1(X2,sK4)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f1696,plain,
    ( ? [X2] :
        ( ~ r2_hidden(sK3,k2_relat_1(sK4))
        & r2_hidden(sK3,k2_relat_1(k5_relat_1(X2,sK4)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(sK3,k2_relat_1(sK4))
      & r2_hidden(sK3,k2_relat_1(k5_relat_1(sK5,sK4)))
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f933,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f932])).

fof(f932,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f914])).

fof(f914,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f913])).

fof(f913,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).

fof(f4916,plain,(
    r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f4915,f2189])).

fof(f2189,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f1697])).

fof(f4915,plain,
    ( ~ v1_relat_1(sK5)
    | r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f4914,f2187])).

fof(f2187,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f1697])).

fof(f4914,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK5)
    | r2_hidden(sK3,k2_relat_1(sK4)) ),
    inference(resolution,[],[f2322,f4908])).

fof(f4908,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k5_relat_1(sK5,sK4)),X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f2916,f2191])).

fof(f2191,plain,(
    r2_hidden(sK3,k2_relat_1(k5_relat_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f1697])).

fof(f2916,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1942])).

fof(f1942,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK100(X0,X1),X1)
          & r2_hidden(sK100(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK100])],[f1940,f1941])).

fof(f1941,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK100(X0,X1),X1)
        & r2_hidden(sK100(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1940,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1939])).

fof(f1939,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1413])).

fof(f1413,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f2322,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f987])).

fof(f987,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f844])).

fof(f844,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
%------------------------------------------------------------------------------
