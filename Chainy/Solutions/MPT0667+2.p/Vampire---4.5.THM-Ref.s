%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0667+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 2.62s
% Output     : Refutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   31 (  57 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 ( 211 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8226,plain,(
    $false ),
    inference(resolution,[],[f8201,f1249])).

fof(f1249,plain,(
    ~ v2_funct_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f1165])).

fof(f1165,plain,
    ( ~ v2_funct_1(k7_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f977,f1164])).

fof(f1164,plain,
    ( ? [X0,X1] :
        ( ~ v2_funct_1(k7_relat_1(X1,X0))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k7_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f977,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k7_relat_1(X1,X0))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f976])).

fof(f976,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k7_relat_1(X1,X0))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f971])).

fof(f971,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f970])).

fof(f970,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k7_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_funct_1)).

fof(f8201,plain,(
    ! [X0] : v2_funct_1(k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f8200,f1544])).

fof(f1544,plain,(
    ! [X35] : k7_relat_1(sK1,X35) = k5_relat_1(k6_relat_1(X35),sK1) ),
    inference(resolution,[],[f1246,f1292])).

fof(f1292,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f1032])).

fof(f1032,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f883])).

fof(f883,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1246,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1165])).

fof(f8200,plain,(
    ! [X0] : v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1)) ),
    inference(subsumption_resolution,[],[f8199,f1485])).

fof(f1485,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f903])).

fof(f903,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f8199,plain,(
    ! [X0] :
      ( v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f8184,f1486])).

fof(f1486,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f903])).

fof(f8184,plain,(
    ! [X0] :
      ( v2_funct_1(k5_relat_1(k6_relat_1(X0),sK1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f1700,f1388])).

fof(f1388,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f948])).

fof(f948,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f1700,plain,(
    ! [X7] :
      ( ~ v2_funct_1(X7)
      | v2_funct_1(k5_relat_1(X7,sK1))
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f1699,f1246])).

fof(f1699,plain,(
    ! [X7] :
      ( v2_funct_1(k5_relat_1(X7,sK1))
      | ~ v2_funct_1(X7)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f1670,f1247])).

fof(f1247,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1165])).

fof(f1670,plain,(
    ! [X7] :
      ( v2_funct_1(k5_relat_1(X7,sK1))
      | ~ v2_funct_1(X7)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f1248,f1336])).

fof(f1336,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1073])).

fof(f1073,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1072])).

fof(f1072,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f942])).

fof(f942,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

fof(f1248,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1165])).
%------------------------------------------------------------------------------
