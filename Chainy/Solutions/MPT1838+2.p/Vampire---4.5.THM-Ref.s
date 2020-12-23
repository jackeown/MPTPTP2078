%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1838+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:33 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 126 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  185 ( 525 expanded)
%              Number of equality atoms :   61 ( 134 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8784,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8783,f4269])).

fof(f4269,plain,(
    sK2 != sK3 ),
    inference(literal_reordering,[],[f3922])).

fof(f3922,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f3773])).

fof(f3773,plain,
    ( sK2 != sK3
    & r1_tarski(sK2,sK3)
    & v1_zfmisc_1(sK3)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f3560,f3772,f3771])).

fof(f3771,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK2 != X1
          & r1_tarski(sK2,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3772,plain,
    ( ? [X1] :
        ( sK2 != X1
        & r1_tarski(sK2,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK2 != sK3
      & r1_tarski(sK2,sK3)
      & v1_zfmisc_1(sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3560,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3559])).

fof(f3559,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3549])).

fof(f3549,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f3548])).

fof(f3548,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f8783,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f8758,f6106])).

fof(f6106,plain,(
    k1_xboole_0 != sK2 ),
    inference(superposition,[],[f4582,f5402])).

fof(f5402,plain,(
    sK2 = k2_xboole_0(k1_tarski(sK17(sK2)),sK2) ),
    inference(resolution,[],[f5354,f4577])).

fof(f4577,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(literal_reordering,[],[f4226])).

fof(f4226,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3761])).

fof(f3761,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f304])).

fof(f304,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f5354,plain,(
    r2_hidden(sK17(sK2),sK2) ),
    inference(resolution,[],[f4273,f4345])).

fof(f4345,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK17(X0),X0) ) ),
    inference(literal_reordering,[],[f3995])).

fof(f3995,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK17(X0),X0) ) ),
    inference(cnf_transformation,[],[f3813])).

fof(f3813,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK17(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f3811,f3812])).

fof(f3812,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK17(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3811,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f3810])).

fof(f3810,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f4273,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(literal_reordering,[],[f3918])).

fof(f3918,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f3773])).

fof(f4582,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(literal_reordering,[],[f4231])).

fof(f4231,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f8758,plain,
    ( k1_xboole_0 = sK2
    | sK2 = sK3 ),
    inference(resolution,[],[f6218,f4270])).

fof(f4270,plain,(
    r1_tarski(sK2,sK3) ),
    inference(literal_reordering,[],[f3921])).

fof(f3921,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f3773])).

fof(f6218,plain,(
    ! [X15] :
      ( ~ r1_tarski(X15,sK3)
      | k1_xboole_0 = X15
      | sK3 = X15 ) ),
    inference(superposition,[],[f4563,f6203])).

fof(f6203,plain,(
    sK3 = k1_tarski(sK12(sK3)) ),
    inference(forward_demodulation,[],[f5576,f5583])).

fof(f5583,plain,(
    sK3 = k6_domain_1(sK3,sK12(sK3)) ),
    inference(subsumption_resolution,[],[f5345,f4272])).

fof(f4272,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(literal_reordering,[],[f3919])).

fof(f3919,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f3773])).

fof(f5345,plain,
    ( sK3 = k6_domain_1(sK3,sK12(sK3))
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f4271,f4318])).

fof(f4318,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK12(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(literal_reordering,[],[f3967])).

fof(f3967,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK12(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3800])).

fof(f3800,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK12(X0)) = X0
            & m1_subset_1(sK12(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f3798,f3799])).

fof(f3799,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK12(X0)) = X0
        & m1_subset_1(sK12(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3798,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f3797])).

fof(f3797,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f3589])).

fof(f3589,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3544])).

fof(f3544,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f4271,plain,(
    v1_zfmisc_1(sK3) ),
    inference(literal_reordering,[],[f3920])).

fof(f3920,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f3773])).

fof(f5576,plain,(
    k6_domain_1(sK3,sK12(sK3)) = k1_tarski(sK12(sK3)) ),
    inference(subsumption_resolution,[],[f5571,f4272])).

fof(f5571,plain,
    ( k6_domain_1(sK3,sK12(sK3)) = k1_tarski(sK12(sK3))
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f5567,f4543])).

fof(f4543,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(literal_reordering,[],[f4192])).

fof(f4192,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3749])).

fof(f3749,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3748])).

fof(f3748,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1935])).

fof(f1935,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f5567,plain,(
    m1_subset_1(sK12(sK3),sK3) ),
    inference(subsumption_resolution,[],[f5344,f4272])).

fof(f5344,plain,
    ( m1_subset_1(sK12(sK3),sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f4271,f4319])).

fof(f4319,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK12(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(literal_reordering,[],[f3966])).

fof(f3966,plain,(
    ! [X0] :
      ( m1_subset_1(sK12(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3800])).

fof(f4563,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(literal_reordering,[],[f4210])).

fof(f4210,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f3909])).

fof(f3909,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f3908])).

fof(f3908,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f397])).

fof(f397,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
%------------------------------------------------------------------------------
