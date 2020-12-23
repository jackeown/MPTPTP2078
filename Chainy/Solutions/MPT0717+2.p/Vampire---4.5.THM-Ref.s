%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0717+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  63 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 285 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1760,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1748,f1195])).

fof(f1195,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f1121])).

fof(f1121,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
    & r2_hidden(sK2,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1051,f1120,f1119])).

fof(f1119,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
            & r2_hidden(X2,k1_relat_1(X1)) )
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
          & r2_hidden(X2,k1_relat_1(sK1)) )
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1120,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
        & r2_hidden(X2,k1_relat_1(sK1)) )
   => ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
      & r2_hidden(sK2,k1_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f1051,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1050])).

fof(f1050,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f989])).

fof(f989,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f988])).

fof(f988,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f1748,plain,(
    r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(resolution,[],[f1540,f1567])).

fof(f1567,plain,(
    r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1566,f1191])).

fof(f1191,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1121])).

fof(f1566,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1545,f1193])).

fof(f1193,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1121])).

fof(f1545,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f1194,f1219])).

fof(f1219,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1080])).

fof(f1080,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1079])).

fof(f1079,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f950])).

fof(f950,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f1194,plain,(
    r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1121])).

fof(f1540,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f1535,f1191])).

fof(f1535,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1192,f1297])).

fof(f1297,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1115])).

fof(f1115,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1114])).

fof(f1114,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f806])).

fof(f806,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(f1192,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f1121])).
%------------------------------------------------------------------------------
