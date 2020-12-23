%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:51 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 339 expanded)
%              Number of leaves         :   13 (  62 expanded)
%              Depth                    :   27
%              Number of atoms          :  252 (1572 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f753,plain,(
    $false ),
    inference(subsumption_resolution,[],[f752,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(f752,plain,(
    ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f751,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f751,plain,(
    ~ v1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f750,f39])).

fof(f750,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f749,f40])).

fof(f40,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f749,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f748,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f748,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(global_subsumption,[],[f388,f396,f747])).

fof(f747,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f746,f57])).

fof(f57,plain,(
    ! [X6] : k2_relat_1(k7_relat_1(sK0,X6)) = k9_relat_1(sK0,X6) ),
    inference(resolution,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f746,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f745,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f745,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f744,f38])).

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f744,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f742,f399])).

fof(f399,plain,(
    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f397,f39])).

fof(f397,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f396,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f742,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) ),
    inference(superposition,[],[f43,f406])).

fof(f406,plain,(
    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(subsumption_resolution,[],[f405,f39])).

fof(f405,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f404,f37])).

fof(f404,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f391,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f391,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f389,f166])).

fof(f166,plain,(
    ! [X10] : k7_relat_1(k5_relat_1(sK0,sK1),X10) = k5_relat_1(k7_relat_1(sK0,X10),sK1) ),
    inference(resolution,[],[f129,f39])).

fof(f129,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1) ) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f389,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f387,f46])).

fof(f387,plain,(
    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f385,f76])).

fof(f76,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f69,f39])).

fof(f69,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k1_relat_1(k5_relat_1(X7,sK1)) = k10_relat_1(X7,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f385,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f384,f35])).

fof(f35,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f384,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f383,f39])).

fof(f383,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f382,f40])).

fof(f382,plain,
    ( ~ v1_funct_1(sK0)
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f396,plain,(
    r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f395,f39])).

fof(f395,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f393,f37])).

fof(f393,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f392,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f392,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
      | r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f52,f390])).

fof(f390,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f387,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f388,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(resolution,[],[f387,f34])).

fof(f34,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:59:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (15480)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.49  % (15488)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.50  % (15491)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (15475)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.14/0.51  % (15474)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.14/0.51  % (15479)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.14/0.52  % (15483)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.14/0.52  % (15492)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.14/0.52  % (15490)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.14/0.52  % (15475)Refutation not found, incomplete strategy% (15475)------------------------------
% 1.14/0.52  % (15475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.52  % (15475)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.52  
% 1.14/0.52  % (15475)Memory used [KB]: 10618
% 1.14/0.52  % (15475)Time elapsed: 0.098 s
% 1.14/0.52  % (15475)------------------------------
% 1.14/0.52  % (15475)------------------------------
% 1.14/0.52  % (15495)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.14/0.52  % (15476)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.14/0.52  % (15482)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.14/0.52  % (15485)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.14/0.52  % (15487)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.14/0.52  % (15477)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.14/0.52  % (15473)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.14/0.53  % (15484)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.14/0.53  % (15478)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.14/0.53  % (15482)Refutation not found, incomplete strategy% (15482)------------------------------
% 1.14/0.53  % (15482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.14/0.53  % (15482)Termination reason: Refutation not found, incomplete strategy
% 1.14/0.53  
% 1.14/0.53  % (15482)Memory used [KB]: 10618
% 1.14/0.53  % (15482)Time elapsed: 0.115 s
% 1.14/0.53  % (15482)------------------------------
% 1.14/0.53  % (15482)------------------------------
% 1.14/0.53  % (15481)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.24/0.53  % (15489)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.24/0.53  % (15494)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.24/0.54  % (15472)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.24/0.54  % (15493)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.24/0.54  % (15495)Refutation not found, incomplete strategy% (15495)------------------------------
% 1.24/0.54  % (15495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (15495)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (15495)Memory used [KB]: 10618
% 1.24/0.54  % (15495)Time elapsed: 0.123 s
% 1.24/0.54  % (15495)------------------------------
% 1.24/0.54  % (15495)------------------------------
% 1.24/0.55  % (15486)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 2.07/0.64  % (15485)Refutation found. Thanks to Tanya!
% 2.07/0.64  % SZS status Theorem for theBenchmark
% 2.07/0.64  % SZS output start Proof for theBenchmark
% 2.07/0.64  fof(f753,plain,(
% 2.07/0.64    $false),
% 2.07/0.64    inference(subsumption_resolution,[],[f752,f39])).
% 2.07/0.64  fof(f39,plain,(
% 2.07/0.64    v1_relat_1(sK0)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f16,plain,(
% 2.07/0.64    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.07/0.64    inference(flattening,[],[f15])).
% 2.07/0.64  fof(f15,plain,(
% 2.07/0.64    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.07/0.64    inference(ennf_transformation,[],[f14])).
% 2.07/0.64  fof(f14,negated_conjecture,(
% 2.07/0.64    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 2.07/0.64    inference(negated_conjecture,[],[f13])).
% 2.07/0.64  fof(f13,conjecture,(
% 2.07/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).
% 2.07/0.64  fof(f752,plain,(
% 2.07/0.64    ~v1_relat_1(sK0)),
% 2.07/0.64    inference(resolution,[],[f751,f44])).
% 2.07/0.64  fof(f44,plain,(
% 2.07/0.64    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f21])).
% 2.07/0.64  fof(f21,plain,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(ennf_transformation,[],[f4])).
% 2.07/0.64  fof(f4,axiom,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.07/0.64  fof(f751,plain,(
% 2.07/0.64    ~v1_relat_1(k7_relat_1(sK0,sK2))),
% 2.07/0.64    inference(subsumption_resolution,[],[f750,f39])).
% 2.07/0.64  fof(f750,plain,(
% 2.07/0.64    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK0)),
% 2.07/0.64    inference(subsumption_resolution,[],[f749,f40])).
% 2.07/0.64  fof(f40,plain,(
% 2.07/0.64    v1_funct_1(sK0)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f749,plain,(
% 2.07/0.64    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 2.07/0.64    inference(resolution,[],[f748,f50])).
% 2.07/0.64  fof(f50,plain,(
% 2.07/0.64    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f28])).
% 2.07/0.64  fof(f28,plain,(
% 2.07/0.64    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(flattening,[],[f27])).
% 2.07/0.64  fof(f27,plain,(
% 2.07/0.64    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.64    inference(ennf_transformation,[],[f10])).
% 2.07/0.64  fof(f10,axiom,(
% 2.07/0.64    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 2.07/0.64  fof(f748,plain,(
% 2.07/0.64    ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(k7_relat_1(sK0,sK2))),
% 2.07/0.64    inference(global_subsumption,[],[f388,f396,f747])).
% 2.07/0.64  fof(f747,plain,(
% 2.07/0.64    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2))),
% 2.07/0.64    inference(forward_demodulation,[],[f746,f57])).
% 2.07/0.64  fof(f57,plain,(
% 2.07/0.64    ( ! [X6] : (k2_relat_1(k7_relat_1(sK0,X6)) = k9_relat_1(sK0,X6)) )),
% 2.07/0.64    inference(resolution,[],[f45,f39])).
% 2.07/0.64  fof(f45,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f22,plain,(
% 2.07/0.64    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f6])).
% 2.07/0.64  fof(f6,axiom,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.07/0.64  fof(f746,plain,(
% 2.07/0.64    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.07/0.64    inference(subsumption_resolution,[],[f745,f37])).
% 2.07/0.64  fof(f37,plain,(
% 2.07/0.64    v1_relat_1(sK1)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f745,plain,(
% 2.07/0.64    ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.07/0.64    inference(subsumption_resolution,[],[f744,f38])).
% 2.07/0.64  fof(f38,plain,(
% 2.07/0.64    v1_funct_1(sK1)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f744,plain,(
% 2.07/0.64    ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.07/0.64    inference(subsumption_resolution,[],[f742,f399])).
% 2.07/0.64  fof(f399,plain,(
% 2.07/0.64    sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 2.07/0.64    inference(subsumption_resolution,[],[f397,f39])).
% 2.07/0.64  fof(f397,plain,(
% 2.07/0.64    ~v1_relat_1(sK0) | sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 2.07/0.64    inference(resolution,[],[f396,f46])).
% 2.07/0.64  fof(f46,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 2.07/0.64    inference(cnf_transformation,[],[f24])).
% 2.07/0.64  fof(f24,plain,(
% 2.07/0.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.07/0.64    inference(flattening,[],[f23])).
% 2.07/0.64  fof(f23,plain,(
% 2.07/0.64    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f9])).
% 2.07/0.64  fof(f9,axiom,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 2.07/0.64  fof(f742,plain,(
% 2.07/0.64    sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))),
% 2.07/0.64    inference(superposition,[],[f43,f406])).
% 2.07/0.64  fof(f406,plain,(
% 2.07/0.64    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 2.07/0.64    inference(subsumption_resolution,[],[f405,f39])).
% 2.07/0.64  fof(f405,plain,(
% 2.07/0.64    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK0)),
% 2.07/0.64    inference(subsumption_resolution,[],[f404,f37])).
% 2.07/0.64  fof(f404,plain,(
% 2.07/0.64    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 2.07/0.64    inference(resolution,[],[f391,f51])).
% 2.07/0.64  fof(f51,plain,(
% 2.07/0.64    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f30])).
% 2.07/0.64  fof(f30,plain,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(flattening,[],[f29])).
% 2.07/0.64  fof(f29,plain,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.07/0.64    inference(ennf_transformation,[],[f3])).
% 2.07/0.64  fof(f3,axiom,(
% 2.07/0.64    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.07/0.64  fof(f391,plain,(
% 2.07/0.64    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 2.07/0.64    inference(forward_demodulation,[],[f389,f166])).
% 2.07/0.64  fof(f166,plain,(
% 2.07/0.64    ( ! [X10] : (k7_relat_1(k5_relat_1(sK0,sK1),X10) = k5_relat_1(k7_relat_1(sK0,X10),sK1)) )),
% 2.07/0.64    inference(resolution,[],[f129,f39])).
% 2.07/0.64  fof(f129,plain,(
% 2.07/0.64    ( ! [X10,X11] : (~v1_relat_1(X10) | k7_relat_1(k5_relat_1(X10,sK1),X11) = k5_relat_1(k7_relat_1(X10,X11),sK1)) )),
% 2.07/0.64    inference(resolution,[],[f47,f37])).
% 2.07/0.64  fof(f47,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f25])).
% 2.07/0.64  fof(f25,plain,(
% 2.07/0.64    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f5])).
% 2.07/0.64  fof(f5,axiom,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 2.07/0.64  fof(f389,plain,(
% 2.07/0.64    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))),
% 2.07/0.64    inference(resolution,[],[f387,f46])).
% 2.07/0.64  fof(f387,plain,(
% 2.07/0.64    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.07/0.64    inference(duplicate_literal_removal,[],[f386])).
% 2.07/0.64  fof(f386,plain,(
% 2.07/0.64    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.07/0.64    inference(forward_demodulation,[],[f385,f76])).
% 2.07/0.64  fof(f76,plain,(
% 2.07/0.64    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 2.07/0.64    inference(resolution,[],[f69,f39])).
% 2.07/0.64  fof(f69,plain,(
% 2.07/0.64    ( ! [X7] : (~v1_relat_1(X7) | k1_relat_1(k5_relat_1(X7,sK1)) = k10_relat_1(X7,k1_relat_1(sK1))) )),
% 2.07/0.64    inference(resolution,[],[f42,f37])).
% 2.07/0.64  fof(f42,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f18])).
% 2.07/0.64  fof(f18,plain,(
% 2.07/0.64    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(ennf_transformation,[],[f7])).
% 2.07/0.64  fof(f7,axiom,(
% 2.07/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.07/0.64  fof(f385,plain,(
% 2.07/0.64    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.07/0.64    inference(subsumption_resolution,[],[f384,f35])).
% 2.07/0.64  fof(f35,plain,(
% 2.07/0.64    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | r1_tarski(sK2,k1_relat_1(sK0))),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f384,plain,(
% 2.07/0.64    ~r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.07/0.64    inference(subsumption_resolution,[],[f383,f39])).
% 2.07/0.64  fof(f383,plain,(
% 2.07/0.64    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.07/0.64    inference(subsumption_resolution,[],[f382,f40])).
% 2.07/0.64  fof(f382,plain,(
% 2.07/0.64    ~v1_funct_1(sK0) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.07/0.64    inference(resolution,[],[f53,f36])).
% 2.07/0.64  fof(f36,plain,(
% 2.07/0.64    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f53,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f33])).
% 2.07/0.64  fof(f33,plain,(
% 2.07/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.07/0.64    inference(flattening,[],[f32])).
% 2.07/0.64  fof(f32,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.07/0.64    inference(ennf_transformation,[],[f11])).
% 2.07/0.64  fof(f11,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 2.07/0.64  fof(f43,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f20])).
% 2.07/0.64  fof(f20,plain,(
% 2.07/0.64    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(flattening,[],[f19])).
% 2.07/0.64  fof(f19,plain,(
% 2.07/0.64    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.64    inference(ennf_transformation,[],[f12])).
% 2.07/0.64  fof(f12,axiom,(
% 2.07/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 2.07/0.64  fof(f396,plain,(
% 2.07/0.64    r1_tarski(sK2,k1_relat_1(sK0))),
% 2.07/0.64    inference(subsumption_resolution,[],[f395,f39])).
% 2.07/0.64  fof(f395,plain,(
% 2.07/0.64    r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 2.07/0.64    inference(subsumption_resolution,[],[f393,f37])).
% 2.07/0.64  fof(f393,plain,(
% 2.07/0.64    r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 2.07/0.64    inference(resolution,[],[f392,f41])).
% 2.07/0.64  fof(f41,plain,(
% 2.07/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f17])).
% 2.07/0.64  fof(f17,plain,(
% 2.07/0.64    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(ennf_transformation,[],[f8])).
% 2.07/0.64  fof(f8,axiom,(
% 2.07/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 2.07/0.64  fof(f392,plain,(
% 2.07/0.64    ( ! [X0] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) | r1_tarski(sK2,X0)) )),
% 2.07/0.64    inference(superposition,[],[f52,f390])).
% 2.07/0.64  fof(f390,plain,(
% 2.07/0.64    k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 2.07/0.64    inference(resolution,[],[f387,f48])).
% 2.07/0.64  fof(f48,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.07/0.64    inference(cnf_transformation,[],[f26])).
% 2.07/0.64  fof(f26,plain,(
% 2.07/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f2])).
% 2.07/0.64  fof(f2,axiom,(
% 2.07/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.07/0.64  fof(f52,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f31])).
% 2.07/0.64  fof(f31,plain,(
% 2.07/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.07/0.64    inference(ennf_transformation,[],[f1])).
% 2.07/0.64  fof(f1,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.07/0.64  fof(f388,plain,(
% 2.07/0.64    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0))),
% 2.07/0.64    inference(resolution,[],[f387,f34])).
% 2.07/0.64  fof(f34,plain,(
% 2.07/0.64    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0))),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  % SZS output end Proof for theBenchmark
% 2.07/0.64  % (15485)------------------------------
% 2.07/0.64  % (15485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (15485)Termination reason: Refutation
% 2.07/0.64  
% 2.07/0.64  % (15485)Memory used [KB]: 7931
% 2.07/0.64  % (15485)Time elapsed: 0.206 s
% 2.07/0.64  % (15485)------------------------------
% 2.07/0.64  % (15485)------------------------------
% 2.07/0.64  % (15471)Success in time 0.275 s
%------------------------------------------------------------------------------
