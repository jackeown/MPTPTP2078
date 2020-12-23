%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0624+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 2.84s
% Output     : Refutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   30 (  64 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 326 expanded)
%              Number of equality atoms :   10 (  46 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3174,plain,(
    $false ),
    inference(global_subsumption,[],[f1478,f3173])).

fof(f3173,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f3171])).

fof(f3171,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f2304,f1528])).

fof(f1528,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK12(X0,X1),X1)
          & r2_hidden(sK12(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f1273,f1274])).

fof(f1274,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK12(X0,X1),X1)
        & r2_hidden(sK12(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1273,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1272])).

fof(f1272,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f953])).

fof(f953,plain,(
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

fof(f2304,plain,(
    ! [X42] :
      ( ~ r2_hidden(sK12(X42,k2_relat_1(sK1)),sK0)
      | r1_tarski(X42,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f2229,f1529])).

fof(f1529,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK12(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1275])).

fof(f2229,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_relat_1(sK1))
      | ~ r2_hidden(X1,sK0) ) ),
    inference(global_subsumption,[],[f1476,f1475,f1474,f2221])).

fof(f2221,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_relat_1(sK1))
      | ~ r2_hidden(sK2(X1),k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f1505,f1477])).

fof(f1477,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,sK2(X2)) = X2
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f1247])).

fof(f1247,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    & ! [X2] :
        ( ( k1_funct_1(sK1,sK2(X2)) = X2
          & r2_hidden(sK2(X2),k1_relat_1(sK1)) )
        | ~ r2_hidden(X2,sK0) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f916,f1246,f1245])).

fof(f1245,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k2_relat_1(X1))
        & ! [X2] :
            ( ? [X3] :
                ( k1_funct_1(X1,X3) = X2
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ~ r2_hidden(X2,X0) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k2_relat_1(sK1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(sK1,X3) = X2
              & r2_hidden(X3,k1_relat_1(sK1)) )
          | ~ r2_hidden(X2,sK0) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1246,plain,(
    ! [X2] :
      ( ? [X3] :
          ( k1_funct_1(sK1,X3) = X2
          & r2_hidden(X3,k1_relat_1(sK1)) )
     => ( k1_funct_1(sK1,sK2(X2)) = X2
        & r2_hidden(sK2(X2),k1_relat_1(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f916,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ r2_hidden(X2,X0) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f915])).

fof(f915,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      & ! [X2] :
          ( ? [X3] :
              ( k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ r2_hidden(X2,X0) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f907])).

fof(f907,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ! [X2] :
              ~ ( ! [X3] :
                    ~ ( k1_funct_1(X1,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X1)) )
                & r2_hidden(X2,X0) )
         => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f906])).

fof(f906,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( k1_funct_1(X1,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X1)) )
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

fof(f1505,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f940])).

fof(f940,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f939])).

fof(f939,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f900])).

fof(f900,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f1474,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1247])).

fof(f1475,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1247])).

fof(f1476,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),k1_relat_1(sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f1247])).

fof(f1478,plain,(
    ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1247])).
%------------------------------------------------------------------------------
