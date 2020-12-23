%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0640+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:21 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 312 expanded)
%              Number of leaves         :    5 (  54 expanded)
%              Depth                    :   41
%              Number of atoms          :  326 (1692 expanded)
%              Number of equality atoms :   81 ( 132 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f378,plain,(
    $false ),
    inference(subsumption_resolution,[],[f377,f24])).

fof(f24,plain,(
    ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v2_funct_1(k5_relat_1(X1,X0)) )
             => v2_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

fof(f377,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f376,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f376,plain,
    ( ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f375,f21])).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f375,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(trivial_inequality_removal,[],[f373])).

fof(f373,plain,
    ( sK2(sK1) != sK2(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(superposition,[],[f32,f347])).

fof(f347,plain,(
    sK2(sK1) = sK3(sK1) ),
    inference(subsumption_resolution,[],[f346,f24])).

fof(f346,plain,
    ( sK2(sK1) = sK3(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f345,f20])).

fof(f345,plain,
    ( sK2(sK1) = sK3(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f344,f21])).

fof(f344,plain,
    ( sK2(sK1) = sK3(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f343,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f343,plain,
    ( ~ r2_hidden(sK3(sK1),k1_relat_1(sK1))
    | sK2(sK1) = sK3(sK1) ),
    inference(trivial_inequality_removal,[],[f342])).

fof(f342,plain,
    ( k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ r2_hidden(sK3(sK1),k1_relat_1(sK1))
    | sK2(sK1) = sK3(sK1) ),
    inference(superposition,[],[f340,f101])).

fof(f101,plain,(
    k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) = k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) ),
    inference(forward_demodulation,[],[f100,f39])).

fof(f39,plain,(
    k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1)) ),
    inference(subsumption_resolution,[],[f38,f20])).

fof(f38,plain,
    ( k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f37,f21])).

fof(f37,plain,
    ( ~ v1_funct_1(sK1)
    | k1_funct_1(sK1,sK2(sK1)) = k1_funct_1(sK1,sK3(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f31,f24])).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f100,plain,(
    k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK3(sK1))) ),
    inference(subsumption_resolution,[],[f99,f24])).

fof(f99,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK3(sK1)))
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f98,f20])).

fof(f98,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK3(sK1)))
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f94,f21])).

fof(f94,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK3(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK3(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f90,f30])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f87,f20])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) = k1_funct_1(sK0,k1_funct_1(sK1,X0)) ) ),
    inference(resolution,[],[f56,f21])).

fof(f56,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | k1_funct_1(k5_relat_1(X2,sK0),X3) = k1_funct_1(sK0,k1_funct_1(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f53,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | k1_funct_1(k5_relat_1(X2,sK0),X3) = k1_funct_1(sK0,k1_funct_1(X2,X3)) ) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f340,plain,(
    ! [X0] :
      ( k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK2(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f339,f20])).

fof(f339,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | sK2(sK1) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f338,f26])).

fof(f338,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | sK2(sK1) = X0
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f337,f25])).

fof(f337,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | sK2(sK1) = X0
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f335,f21])).

fof(f335,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | sK2(sK1) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f334,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f334,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | sK2(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f333,f20])).

fof(f333,plain,(
    ! [X0] :
      ( k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f332,f26])).

fof(f332,plain,(
    ! [X0] :
      ( k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f331,f25])).

fof(f331,plain,(
    ! [X0] :
      ( k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f330,f21])).

fof(f330,plain,(
    ! [X0] :
      ( k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f329,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f329,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f328,f24])).

fof(f328,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0
      | v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f327,f20])).

fof(f327,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0
      | ~ v1_relat_1(sK1)
      | v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f326,f21])).

fof(f326,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f106,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK1),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0 ) ),
    inference(forward_demodulation,[],[f105,f42])).

fof(f42,plain,(
    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f41,f20])).

fof(f41,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f40,f25])).

fof(f40,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ r2_hidden(sK2(sK1),k1_relat_1(k5_relat_1(sK1,sK0)))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0 ) ),
    inference(forward_demodulation,[],[f104,f42])).

fof(f104,plain,(
    ! [X0] :
      ( k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK0)))
      | ~ r2_hidden(sK2(sK1),k1_relat_1(k5_relat_1(sK1,sK0)))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f102,f22])).

fof(f22,plain,(
    v2_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0] :
      ( k1_funct_1(k5_relat_1(sK1,sK0),X0) != k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
      | ~ v1_funct_1(k5_relat_1(sK1,sK0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK1,sK0)))
      | ~ r2_hidden(sK2(sK1),k1_relat_1(k5_relat_1(sK1,sK0)))
      | ~ v1_relat_1(k5_relat_1(sK1,sK0))
      | sK2(sK1) = X0
      | ~ v2_funct_1(k5_relat_1(sK1,sK0)) ) ),
    inference(superposition,[],[f28,f97])).

fof(f97,plain,(
    k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1))) ),
    inference(subsumption_resolution,[],[f96,f24])).

fof(f96,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f95,f20])).

fof(f95,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f93,f21])).

fof(f93,plain,
    ( k1_funct_1(k5_relat_1(sK1,sK0),sK2(sK1)) = k1_funct_1(sK0,k1_funct_1(sK1,sK2(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f90,f29])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
