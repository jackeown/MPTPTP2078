%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 676 expanded)
%              Number of leaves         :   15 ( 181 expanded)
%              Depth                    :   33
%              Number of atoms          :  386 (2998 expanded)
%              Number of equality atoms :   78 ( 642 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(subsumption_resolution,[],[f157,f42])).

fof(f42,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f157,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f156,f43])).

fof(f43,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f156,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f155,f146])).

fof(f146,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f45,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f141,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(superposition,[],[f82,f138])).

fof(f138,plain,(
    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f137,f108])).

fof(f108,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f107,f45])).

fof(f107,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f103,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f103,plain,
    ( r1_tarski(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f97,f42])).

fof(f97,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | sK1 = k1_wellord1(k1_wellord2(X1),sK1)
      | r1_tarski(X1,sK1) ) ),
    inference(resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X0),X1) = X1
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(X0),X1) = X1
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f93,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(X0),X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X0),X1) = X1
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f137,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f136,f43])).

fof(f136,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f135,f42])).

fof(f135,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f134,f61])).

fof(f134,plain,
    ( r1_ordinal1(sK1,sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f133,f43])).

fof(f133,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f132,f42])).

fof(f132,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f131,f50])).

fof(f131,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f130,f43])).

fof(f130,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f129,f90])).

fof(f90,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    inference(resolution,[],[f89,f44])).

fof(f44,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0)) ) ),
    inference(resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r4_wellord1(k1_wellord2(X0),X1)
      | r4_wellord1(X1,k1_wellord2(X0)) ) ),
    inference(resolution,[],[f48,f46])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f129,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(superposition,[],[f128,f105])).

fof(f105,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    inference(resolution,[],[f103,f102])).

fof(f102,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f101,f45])).

fof(f101,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f99,f65])).

fof(f99,plain,
    ( r1_tarski(sK1,sK0)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    inference(resolution,[],[f96,f43])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | sK0 = k1_wellord1(k1_wellord2(X0),sK0)
      | r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f95,f42])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f127,f86])).

fof(f86,plain,(
    ! [X4,X3] : k1_wellord2(k1_wellord1(k1_wellord2(X3),X4)) = k2_wellord1(k1_wellord2(X3),k1_wellord1(k1_wellord2(X3),X4)) ),
    inference(resolution,[],[f60,f79])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f52,f77])).

fof(f77,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f46,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f126,f77])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f125,f46])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f82,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_wellord1(k1_wellord2(X3),X4))
      | k1_wellord1(k1_wellord2(X3),X4) = X3 ) ),
    inference(resolution,[],[f65,f79])).

fof(f155,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f154,f61])).

fof(f154,plain,(
    r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f153,f42])).

fof(f153,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f152,f43])).

fof(f152,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f145,f50])).

fof(f145,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f144,f42])).

fof(f144,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f139,f44])).

fof(f139,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(superposition,[],[f128,f138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (8038)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (8038)Refutation not found, incomplete strategy% (8038)------------------------------
% 0.21/0.46  % (8038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8038)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (8038)Memory used [KB]: 6140
% 0.21/0.46  % (8038)Time elapsed: 0.054 s
% 0.21/0.46  % (8038)------------------------------
% 0.21/0.46  % (8038)------------------------------
% 0.21/0.47  % (8046)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.47  % (8046)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f157,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    v3_ordinal1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f32,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~v3_ordinal1(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f156,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    v3_ordinal1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f155,f146])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f141,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    sK0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.21/0.47    inference(superposition,[],[f82,f138])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f137,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ~r1_tarski(sK1,sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f107,f45])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~r1_tarski(sK1,sK0) | sK0 = sK1),
% 0.21/0.47    inference(resolution,[],[f103,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.47    inference(flattening,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.47    inference(resolution,[],[f97,f42])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X1] : (~v3_ordinal1(X1) | sK1 = k1_wellord1(k1_wellord2(X1),sK1) | r1_tarski(X1,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f95,f43])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X0),X1) = X1 | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(X0),X1) = X1 | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(resolution,[],[f93,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(X0),X1) = X1) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X0),X1) = X1 | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(resolution,[],[f51,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f136,f43])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f135,f42])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.47    inference(resolution,[],[f134,f61])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    r1_ordinal1(sK1,sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f133,f43])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f132,f42])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.21/0.47    inference(resolution,[],[f131,f50])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f130,f43])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f129,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.21/0.47    inference(resolution,[],[f89,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | r4_wellord1(k1_wellord2(X1),k1_wellord2(X0))) )),
% 0.21/0.47    inference(resolution,[],[f83,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r4_wellord1(k1_wellord2(X0),X1) | r4_wellord1(X1,k1_wellord2(X0))) )),
% 0.21/0.47    inference(resolution,[],[f48,f46])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | r4_wellord1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.47    inference(superposition,[],[f128,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.47    inference(resolution,[],[f103,f102])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f101,f45])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.21/0.47    inference(resolution,[],[f99,f65])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    r1_tarski(sK1,sK0) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.47    inference(resolution,[],[f96,f43])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X0] : (~v3_ordinal1(X0) | sK0 = k1_wellord1(k1_wellord2(X0),sK0) | r1_tarski(X0,sK0)) )),
% 0.21/0.47    inference(resolution,[],[f95,f42])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X1),k1_wellord2(k1_wellord1(k1_wellord2(X1),X0))) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f127,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k1_wellord2(k1_wellord1(k1_wellord2(X3),X4)) = k2_wellord1(k1_wellord2(X3),k1_wellord1(k1_wellord2(X3),X4))) )),
% 0.21/0.47    inference(resolution,[],[f60,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f78,f46])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_wellord1(k1_wellord2(X0),X1),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.47    inference(superposition,[],[f52,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.47    inference(global_subsumption,[],[f46,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.47    inference(equality_resolution,[],[f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(rectify,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v3_ordinal1(X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f126,f77])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v3_ordinal1(X1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f125,f46])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.21/0.47    inference(resolution,[],[f47,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X4,X3] : (~r1_tarski(X3,k1_wellord1(k1_wellord2(X3),X4)) | k1_wellord1(k1_wellord2(X3),X4) = X3) )),
% 0.21/0.47    inference(resolution,[],[f65,f79])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.47    inference(resolution,[],[f154,f61])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    r1_ordinal1(sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f153,f42])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f152,f43])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.21/0.47    inference(resolution,[],[f145,f50])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ~r2_hidden(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f144,f42])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f139,f44])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.47    inference(superposition,[],[f128,f138])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (8046)------------------------------
% 0.21/0.47  % (8046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8046)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (8046)Memory used [KB]: 6140
% 0.21/0.47  % (8046)Time elapsed: 0.071 s
% 0.21/0.47  % (8046)------------------------------
% 0.21/0.47  % (8046)------------------------------
% 0.21/0.48  % (8024)Success in time 0.116 s
%------------------------------------------------------------------------------
