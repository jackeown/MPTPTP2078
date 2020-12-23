%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0947+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:57 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   32 (  85 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 493 expanded)
%              Number of equality atoms :   16 (  82 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(global_subsumption,[],[f32,f37])).

fof(f37,plain,(
    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK2)) ),
    inference(unit_resulting_resolution,[],[f19,f28,f29,f28,f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_wellord1(X1,X2)
      | r4_wellord1(X0,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).

fof(f23,plain,(
    r4_wellord1(sK0,k1_wellord2(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != sK2
    & r4_wellord1(sK0,k1_wellord2(sK2))
    & r4_wellord1(sK0,k1_wellord2(sK1))
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r4_wellord1(X0,k1_wellord2(X2))
                & r4_wellord1(X0,k1_wellord2(X1))
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(sK0,k1_wellord2(X2))
              & r4_wellord1(sK0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r4_wellord1(sK0,k1_wellord2(X2))
            & r4_wellord1(sK0,k1_wellord2(X1))
            & v3_ordinal1(X2) )
        & v3_ordinal1(X1) )
   => ( ? [X2] :
          ( sK1 != X2
          & r4_wellord1(sK0,k1_wellord2(X2))
          & r4_wellord1(sK0,k1_wellord2(sK1))
          & v3_ordinal1(X2) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( sK1 != X2
        & r4_wellord1(sK0,k1_wellord2(X2))
        & r4_wellord1(sK0,k1_wellord2(sK1))
        & v3_ordinal1(X2) )
   => ( sK1 != sK2
      & r4_wellord1(sK0,k1_wellord2(sK2))
      & r4_wellord1(sK0,k1_wellord2(sK1))
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r4_wellord1(X0,k1_wellord2(X2))
              & r4_wellord1(X0,k1_wellord2(X1))
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r4_wellord1(X0,k1_wellord2(X2))
                    & r4_wellord1(X0,k1_wellord2(X1)) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r4_wellord1(X0,k1_wellord2(X2))
                  & r4_wellord1(X0,k1_wellord2(X1)) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord2)).

fof(f29,plain,(
    r4_wellord1(k1_wellord2(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f19,f28,f22,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f22,plain,(
    r4_wellord1(sK0,k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f21,f24,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
