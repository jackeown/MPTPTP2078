%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 259 expanded)
%              Number of leaves         :   10 ( 112 expanded)
%              Depth                    :   27
%              Number of atoms          :  314 (2343 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ! [X4] :
        ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
        | ~ r2_hidden(X4,k3_relat_1(sK1)) )
    & r2_hidden(sK3,k3_relat_1(sK0))
    & r3_wellord1(sK0,sK1,sK2)
    & v2_wellord1(sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                        | ~ r2_hidden(X4,k3_relat_1(X1)) )
                    & r2_hidden(X3,k3_relat_1(X0)) )
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(sK0)) )
              & r3_wellord1(sK0,X1,X2)
              & v2_wellord1(sK0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                    | ~ r2_hidden(X4,k3_relat_1(X1)) )
                & r2_hidden(X3,k3_relat_1(sK0)) )
            & r3_wellord1(sK0,X1,X2)
            & v2_wellord1(sK0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
                  | ~ r2_hidden(X4,k3_relat_1(sK1)) )
              & r2_hidden(X3,k3_relat_1(sK0)) )
          & r3_wellord1(sK0,sK1,X2)
          & v2_wellord1(sK0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(sK1)) )
            & r2_hidden(X3,k3_relat_1(sK0)) )
        & r3_wellord1(sK0,sK1,X2)
        & v2_wellord1(sK0)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
              | ~ r2_hidden(X4,k3_relat_1(sK1)) )
          & r2_hidden(X3,k3_relat_1(sK0)) )
      & r3_wellord1(sK0,sK1,sK2)
      & v2_wellord1(sK0)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
            | ~ r2_hidden(X4,k3_relat_1(sK1)) )
        & r2_hidden(X3,k3_relat_1(sK0)) )
   => ( ! [X4] :
          ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
          | ~ r2_hidden(X4,k3_relat_1(sK1)) )
      & r2_hidden(sK3,k3_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => ! [X3] :
                      ~ ( ! [X4] :
                            ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                              & r2_hidden(X4,k3_relat_1(X1)) )
                        & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_wellord1)).

fof(f66,plain,(
    ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f65,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f63,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f62,f27])).

fof(f27,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f61,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_wellord1(sK0,X0),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f40,f23])).

fof(f40,plain,(
    ! [X0] :
      ( r1_tarski(k1_wellord1(sK0,X0),k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f33,f39])).

fof(f39,plain,(
    ! [X0] : k1_wellord1(sK0,X0) = k3_relat_1(k2_wellord1(sK0,k1_wellord1(sK0,X0))) ),
    inference(subsumption_resolution,[],[f38,f23])).

fof(f38,plain,(
    ! [X0] :
      ( k1_wellord1(sK0,X0) = k3_relat_1(k2_wellord1(sK0,k1_wellord1(sK0,X0)))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f35,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

fof(f61,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f60,f28])).

fof(f28,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f29,plain,(
    r2_hidden(sK3,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,
    ( ~ r2_hidden(sK3,k3_relat_1(sK0))
    | ~ r3_wellord1(sK0,sK1,sK2)
    | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
      | ~ r3_wellord1(X1,X2,X3)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( r3_wellord1(X1,X2,X3)
                  & r1_tarski(X0,k3_relat_1(X1))
                  & v2_wellord1(X1) )
               => ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                  & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_wellord1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0))))
      | ~ r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f57,f23])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0))))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0))))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f55,f25])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0))))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0))))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f53,f28])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0))))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ r3_wellord1(sK0,sK1,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0))))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ r3_wellord1(sK0,sK1,sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3))
                    & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f21])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
          & r2_hidden(X4,k3_relat_1(X1)) )
     => ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3))
        & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
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
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_wellord1)).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,sK1,sK2,X0),k3_relat_1(sK1))
      | ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0))))
      | ~ r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(superposition,[],[f30,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0))
      | ~ r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f49,f23])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f48,f24])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f47,f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X1,X2,sK2)
      | ~ r2_hidden(X0,k3_relat_1(X1))
      | k9_relat_1(sK2,k1_wellord1(X1,X0)) = k1_wellord1(X2,sK4(X1,X2,sK2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f46,f25])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(X1))
      | ~ r3_wellord1(X1,X2,sK2)
      | k9_relat_1(sK2,k1_wellord1(X1,X0)) = k1_wellord1(X2,sK4(X1,X2,sK2,X0))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f32,f26])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X4] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
      | ~ r2_hidden(X4,k3_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (18559)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.44  % (18559)Refutation not found, incomplete strategy% (18559)------------------------------
% 0.21/0.44  % (18559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (18559)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (18559)Memory used [KB]: 10490
% 0.21/0.44  % (18559)Time elapsed: 0.056 s
% 0.21/0.44  % (18559)------------------------------
% 0.21/0.44  % (18559)------------------------------
% 0.21/0.45  % (18575)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.45  % (18567)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.45  % (18575)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f66,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    (((! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(sK3,k3_relat_1(sK0))) & r3_wellord1(sK0,sK1,sK2) & v2_wellord1(sK0) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f19,f18,f17,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,X1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,X1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,sK1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,sK1,X2) & v2_wellord1(sK0) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(X3,k3_relat_1(sK0))) & r3_wellord1(sK0,sK1,sK2) & v2_wellord1(sK0) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(X3,k3_relat_1(sK0))) => (! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) & r2_hidden(sK3,k3_relat_1(sK0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & r3_wellord1(X0,X1,X2) & v2_wellord1(X0) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (! [X4] : (~r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) | ~r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0))) & (r3_wellord1(X0,X1,X2) & v2_wellord1(X0))) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => ! [X3] : ~(! [X4] : ~(r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f5])).
% 0.21/0.45  fof(f5,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r3_wellord1(X0,X1,X2) & v2_wellord1(X0)) => ! [X3] : ~(! [X4] : ~(r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4))) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_wellord1)).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ~v1_relat_1(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f65,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f64,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    v1_relat_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f63,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    v1_funct_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f62,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    v2_wellord1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ~v2_wellord1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f61,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k1_wellord1(sK0,X0),k3_relat_1(sK0))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f40,f23])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k1_wellord1(sK0,X0),k3_relat_1(sK0)) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(superposition,[],[f33,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0] : (k1_wellord1(sK0,X0) = k3_relat_1(k2_wellord1(sK0,k1_wellord1(sK0,X0)))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f38,f23])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0] : (k1_wellord1(sK0,X0) = k3_relat_1(k2_wellord1(sK0,k1_wellord1(sK0,X0))) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(resolution,[],[f35,f27])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v2_wellord1(X1) | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : (k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) | ~v2_wellord1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (v2_wellord1(X1) => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f60,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    r3_wellord1(sK0,sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ~r3_wellord1(sK0,sK1,sK2) | ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f59,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    r2_hidden(sK3,k3_relat_1(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ~r2_hidden(sK3,k3_relat_1(sK0)) | ~r3_wellord1(sK0,sK1,sK2) | ~r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) | ~v2_wellord1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(resolution,[],[f58,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) | ~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (! [X3] : ((r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0))) | ~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (! [X3] : (((r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0))) | (~r3_wellord1(X1,X2,X3) | ~r1_tarski(X0,k3_relat_1(X1)) | ~v2_wellord1(X1))) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((r3_wellord1(X1,X2,X3) & r1_tarski(X0,k3_relat_1(X1)) & v2_wellord1(X1)) => (r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0))) & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_wellord1)).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0)))) | ~r2_hidden(X0,k3_relat_1(sK0))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f57,f23])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X0] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0)))) | ~r2_hidden(X0,k3_relat_1(sK0)) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f56,f24])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X0] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0)))) | ~r2_hidden(X0,k3_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f55,f25])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0)))) | ~r2_hidden(X0,k3_relat_1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f54,f26])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0)))) | ~r2_hidden(X0,k3_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f53,f28])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X0] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0)))) | ~r2_hidden(X0,k3_relat_1(sK0)) | ~r3_wellord1(sK0,sK1,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X0] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0)))) | ~r2_hidden(X0,k3_relat_1(sK0)) | ~r2_hidden(X0,k3_relat_1(sK0)) | ~r3_wellord1(sK0,sK1,sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(resolution,[],[f51,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3)) & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X3,X2,X1,X0] : (? [X4] : (k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4) & r2_hidden(X4,k3_relat_1(X1))) => (k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3)) & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (? [X4] : (k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4) & r2_hidden(X4,k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (? [X4] : (k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4) & r2_hidden(X4,k3_relat_1(X1))) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r3_wellord1(X0,X1,X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3] : ~(! [X4] : ~(k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4) & r2_hidden(X4,k3_relat_1(X1))) & r2_hidden(X3,k3_relat_1(X0)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_wellord1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(sK4(sK0,sK1,sK2,X0),k3_relat_1(sK1)) | ~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,X0)))) | ~r2_hidden(X0,k3_relat_1(sK0))) )),
% 0.21/0.45    inference(superposition,[],[f30,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0] : (k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) | ~r2_hidden(X0,k3_relat_1(sK0))) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f49,f23])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f48,f24])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 0.21/0.45    inference(resolution,[],[f47,f28])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r3_wellord1(X1,X2,sK2) | ~r2_hidden(X0,k3_relat_1(X1)) | k9_relat_1(sK2,k1_wellord1(X1,X0)) = k1_wellord1(X2,sK4(X1,X2,sK2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f46,f25])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(X1)) | ~r3_wellord1(X1,X2,sK2) | k9_relat_1(sK2,k1_wellord1(X1,X0)) = k1_wellord1(X2,sK4(X1,X2,sK2,X0)) | ~v1_relat_1(sK2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(resolution,[],[f32,f26])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2) | k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X4] : (~r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4))) | ~r2_hidden(X4,k3_relat_1(sK1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (18575)------------------------------
% 0.21/0.45  % (18575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (18575)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (18575)Memory used [KB]: 6140
% 0.21/0.45  % (18575)Time elapsed: 0.071 s
% 0.21/0.45  % (18575)------------------------------
% 0.21/0.45  % (18575)------------------------------
% 0.21/0.46  % (18555)Success in time 0.097 s
%------------------------------------------------------------------------------
