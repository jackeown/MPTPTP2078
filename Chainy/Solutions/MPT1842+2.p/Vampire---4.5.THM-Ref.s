%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1842+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 139 expanded)
%              Number of leaves         :    8 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 521 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (19452)ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_62 on theBenchmark
fof(f4927,plain,(
    $false ),
    inference(global_subsumption,[],[f4910,f4915,f4918])).

fof(f4918,plain,
    ( sK13 = k1_tarski(sK14)
    | ~ m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13)) ),
    inference(resolution,[],[f4909,f4156])).

fof(f4156,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3936])).

fof(f3936,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f3613])).

fof(f3613,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3547])).

fof(f3547,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f4909,plain,(
    ~ v1_subset_1(k1_tarski(sK14),sK13) ),
    inference(backward_demodulation,[],[f4154,f4736])).

fof(f4736,plain,(
    k6_domain_1(sK13,sK14) = k1_tarski(sK14) ),
    inference(subsumption_resolution,[],[f4725,f4151])).

fof(f4151,plain,(
    ~ v1_xboole_0(sK13) ),
    inference(cnf_transformation,[],[f3935])).

fof(f3935,plain,
    ( ~ v1_subset_1(k6_domain_1(sK13,sK14),sK13)
    & m1_subset_1(sK14,sK13)
    & ~ v1_zfmisc_1(sK13)
    & ~ v1_xboole_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f3612,f3934,f3933])).

fof(f3933,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(sK13,X1),sK13)
          & m1_subset_1(X1,sK13) )
      & ~ v1_zfmisc_1(sK13)
      & ~ v1_xboole_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f3934,plain,
    ( ? [X1] :
        ( ~ v1_subset_1(k6_domain_1(sK13,X1),sK13)
        & m1_subset_1(X1,sK13) )
   => ( ~ v1_subset_1(k6_domain_1(sK13,sK14),sK13)
      & m1_subset_1(sK14,sK13) ) ),
    introduced(choice_axiom,[])).

fof(f3612,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3611])).

fof(f3611,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3557])).

fof(f3557,negated_conjecture,(
    ~ ! [X0] :
        ( ( ~ v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f3556])).

fof(f3556,conjecture,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(f4725,plain,
    ( k6_domain_1(sK13,sK14) = k1_tarski(sK14)
    | v1_xboole_0(sK13) ),
    inference(resolution,[],[f4153,f4169])).

fof(f4169,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3630])).

fof(f3630,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3629])).

fof(f3629,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f4153,plain,(
    m1_subset_1(sK14,sK13) ),
    inference(cnf_transformation,[],[f3935])).

fof(f4154,plain,(
    ~ v1_subset_1(k6_domain_1(sK13,sK14),sK13) ),
    inference(cnf_transformation,[],[f3935])).

fof(f4915,plain,(
    m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13)) ),
    inference(subsumption_resolution,[],[f4914,f4151])).

fof(f4914,plain,
    ( m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13))
    | v1_xboole_0(sK13) ),
    inference(subsumption_resolution,[],[f4912,f4153])).

fof(f4912,plain,
    ( m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13))
    | ~ m1_subset_1(sK14,sK13)
    | v1_xboole_0(sK13) ),
    inference(superposition,[],[f4168,f4736])).

fof(f4168,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3628])).

fof(f3628,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3627])).

fof(f3627,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1893])).

fof(f1893,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f4910,plain,(
    sK13 != k1_tarski(sK14) ),
    inference(superposition,[],[f4738,f4736])).

fof(f4738,plain,(
    sK13 != k6_domain_1(sK13,sK14) ),
    inference(subsumption_resolution,[],[f4737,f4151])).

fof(f4737,plain,
    ( sK13 != k6_domain_1(sK13,sK14)
    | v1_xboole_0(sK13) ),
    inference(subsumption_resolution,[],[f4726,f4152])).

fof(f4152,plain,(
    ~ v1_zfmisc_1(sK13) ),
    inference(cnf_transformation,[],[f3935])).

fof(f4726,plain,
    ( v1_zfmisc_1(sK13)
    | sK13 != k6_domain_1(sK13,sK14)
    | v1_xboole_0(sK13) ),
    inference(resolution,[],[f4153,f4194])).

fof(f4194,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3956])).

fof(f3956,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK23(X0)) = X0
            & m1_subset_1(sK23(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f3954,f3955])).

fof(f3955,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK23(X0)) = X0
        & m1_subset_1(sK23(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3954,plain,(
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
    inference(rectify,[],[f3953])).

fof(f3953,plain,(
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
    inference(nnf_transformation,[],[f3647])).

fof(f3647,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3546])).

fof(f3546,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
%------------------------------------------------------------------------------
