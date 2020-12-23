%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0706+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   25 (  73 expanded)
%              Number of leaves         :    3 (  18 expanded)
%              Depth                    :   14
%              Number of atoms          :   85 ( 397 expanded)
%              Number of equality atoms :   25 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4018,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4017,f2283])).

fof(f2283,plain,(
    v1_relat_1(sK107) ),
    inference(cnf_transformation,[],[f1789])).

fof(f1789,plain,
    ( sK105 != sK106
    & r1_tarski(sK106,k2_relat_1(sK107))
    & r1_tarski(sK105,k2_relat_1(sK107))
    & k10_relat_1(sK107,sK106) = k10_relat_1(sK107,sK105)
    & v1_funct_1(sK107)
    & v1_relat_1(sK107) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK105,sK106,sK107])],[f1029,f1788])).

fof(f1788,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r1_tarski(X1,k2_relat_1(X2))
        & r1_tarski(X0,k2_relat_1(X2))
        & k10_relat_1(X2,X1) = k10_relat_1(X2,X0)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK105 != sK106
      & r1_tarski(sK106,k2_relat_1(sK107))
      & r1_tarski(sK105,k2_relat_1(sK107))
      & k10_relat_1(sK107,sK106) = k10_relat_1(sK107,sK105)
      & v1_funct_1(sK107)
      & v1_relat_1(sK107) ) ),
    introduced(choice_axiom,[])).

fof(f1029,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X1) = k10_relat_1(X2,X0)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1028])).

fof(f1028,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X1) = k10_relat_1(X2,X0)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f965])).

fof(f965,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X1,k2_relat_1(X2))
            & r1_tarski(X0,k2_relat_1(X2))
            & k10_relat_1(X2,X1) = k10_relat_1(X2,X0) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f964])).

fof(f964,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X1,k2_relat_1(X2))
          & r1_tarski(X0,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k10_relat_1(X2,X0) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_1)).

fof(f4017,plain,(
    ~ v1_relat_1(sK107) ),
    inference(subsumption_resolution,[],[f4016,f2284])).

fof(f2284,plain,(
    v1_funct_1(sK107) ),
    inference(cnf_transformation,[],[f1789])).

fof(f4016,plain,
    ( ~ v1_funct_1(sK107)
    | ~ v1_relat_1(sK107) ),
    inference(subsumption_resolution,[],[f4015,f2286])).

fof(f2286,plain,(
    r1_tarski(sK105,k2_relat_1(sK107)) ),
    inference(cnf_transformation,[],[f1789])).

fof(f4015,plain,
    ( ~ r1_tarski(sK105,k2_relat_1(sK107))
    | ~ v1_funct_1(sK107)
    | ~ v1_relat_1(sK107) ),
    inference(subsumption_resolution,[],[f3969,f2288])).

fof(f2288,plain,(
    sK105 != sK106 ),
    inference(cnf_transformation,[],[f1789])).

fof(f3969,plain,
    ( sK105 = sK106
    | ~ r1_tarski(sK105,k2_relat_1(sK107))
    | ~ v1_funct_1(sK107)
    | ~ v1_relat_1(sK107) ),
    inference(superposition,[],[f3710,f2361])).

fof(f2361,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1094])).

fof(f1094,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1093])).

fof(f1093,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f948])).

fof(f948,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f3710,plain,(
    sK106 = k9_relat_1(sK107,k10_relat_1(sK107,sK105)) ),
    inference(subsumption_resolution,[],[f3709,f2283])).

fof(f3709,plain,
    ( sK106 = k9_relat_1(sK107,k10_relat_1(sK107,sK105))
    | ~ v1_relat_1(sK107) ),
    inference(subsumption_resolution,[],[f3708,f2284])).

fof(f3708,plain,
    ( sK106 = k9_relat_1(sK107,k10_relat_1(sK107,sK105))
    | ~ v1_funct_1(sK107)
    | ~ v1_relat_1(sK107) ),
    inference(subsumption_resolution,[],[f3672,f2287])).

fof(f2287,plain,(
    r1_tarski(sK106,k2_relat_1(sK107)) ),
    inference(cnf_transformation,[],[f1789])).

fof(f3672,plain,
    ( sK106 = k9_relat_1(sK107,k10_relat_1(sK107,sK105))
    | ~ r1_tarski(sK106,k2_relat_1(sK107))
    | ~ v1_funct_1(sK107)
    | ~ v1_relat_1(sK107) ),
    inference(superposition,[],[f2361,f2285])).

fof(f2285,plain,(
    k10_relat_1(sK107,sK106) = k10_relat_1(sK107,sK105) ),
    inference(cnf_transformation,[],[f1789])).
%------------------------------------------------------------------------------
