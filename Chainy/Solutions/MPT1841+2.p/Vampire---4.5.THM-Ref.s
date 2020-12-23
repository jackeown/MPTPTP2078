%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1841+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 103 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 397 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4962,plain,(
    $false ),
    inference(global_subsumption,[],[f4947,f4961])).

fof(f4961,plain,(
    ~ m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13)) ),
    inference(subsumption_resolution,[],[f4960,f4160])).

fof(f4160,plain,(
    ~ v1_xboole_0(sK13) ),
    inference(cnf_transformation,[],[f3940])).

fof(f3940,plain,
    ( v1_zfmisc_1(sK13)
    & v1_subset_1(k6_domain_1(sK13,sK14),sK13)
    & m1_subset_1(sK14,sK13)
    & ~ v1_xboole_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f3611,f3939,f3938])).

fof(f3938,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK13)
          & v1_subset_1(k6_domain_1(sK13,X1),sK13)
          & m1_subset_1(X1,sK13) )
      & ~ v1_xboole_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f3939,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK13)
        & v1_subset_1(k6_domain_1(sK13,X1),sK13)
        & m1_subset_1(X1,sK13) )
   => ( v1_zfmisc_1(sK13)
      & v1_subset_1(k6_domain_1(sK13,sK14),sK13)
      & m1_subset_1(sK14,sK13) ) ),
    introduced(choice_axiom,[])).

fof(f3611,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3610])).

fof(f3610,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3555])).

fof(f3555,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f3554])).

fof(f3554,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f4960,plain,
    ( ~ m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13))
    | v1_xboole_0(sK13) ),
    inference(subsumption_resolution,[],[f4959,f4163])).

fof(f4163,plain,(
    v1_zfmisc_1(sK13) ),
    inference(cnf_transformation,[],[f3940])).

fof(f4959,plain,
    ( ~ m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13))
    | ~ v1_zfmisc_1(sK13)
    | v1_xboole_0(sK13) ),
    inference(subsumption_resolution,[],[f4949,f4476])).

fof(f4476,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f293])).

fof(f293,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f4949,plain,
    ( v1_xboole_0(k1_tarski(sK14))
    | ~ m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13))
    | ~ v1_zfmisc_1(sK13)
    | v1_xboole_0(sK13) ),
    inference(resolution,[],[f4943,f4194])).

fof(f4194,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3634])).

fof(f3634,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3633])).

fof(f3633,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3543])).

fof(f3543,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f4943,plain,(
    v1_subset_1(k1_tarski(sK14),sK13) ),
    inference(backward_demodulation,[],[f4162,f4767])).

fof(f4767,plain,(
    k6_domain_1(sK13,sK14) = k1_tarski(sK14) ),
    inference(subsumption_resolution,[],[f4754,f4160])).

fof(f4754,plain,
    ( k6_domain_1(sK13,sK14) = k1_tarski(sK14)
    | v1_xboole_0(sK13) ),
    inference(resolution,[],[f4161,f4203])).

fof(f4203,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3645])).

fof(f3645,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3644])).

fof(f3644,plain,(
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

fof(f4161,plain,(
    m1_subset_1(sK14,sK13) ),
    inference(cnf_transformation,[],[f3940])).

fof(f4162,plain,(
    v1_subset_1(k6_domain_1(sK13,sK14),sK13) ),
    inference(cnf_transformation,[],[f3940])).

fof(f4947,plain,(
    m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13)) ),
    inference(subsumption_resolution,[],[f4946,f4160])).

fof(f4946,plain,
    ( m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13))
    | v1_xboole_0(sK13) ),
    inference(subsumption_resolution,[],[f4944,f4161])).

fof(f4944,plain,
    ( m1_subset_1(k1_tarski(sK14),k1_zfmisc_1(sK13))
    | ~ m1_subset_1(sK14,sK13)
    | v1_xboole_0(sK13) ),
    inference(superposition,[],[f4202,f4767])).

fof(f4202,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3643])).

fof(f3643,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3642])).

fof(f3642,plain,(
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
%------------------------------------------------------------------------------
