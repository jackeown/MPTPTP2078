%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:00 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  111 (1291 expanded)
%              Number of leaves         :   16 ( 391 expanded)
%              Depth                    :   25
%              Number of atoms          :  466 (7315 expanded)
%              Number of equality atoms :  158 (1582 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(subsumption_resolution,[],[f628,f577])).

fof(f577,plain,(
    ! [X3] : k1_xboole_0 = X3 ),
    inference(subsumption_resolution,[],[f573,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f573,plain,(
    ! [X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X3)
      | k1_xboole_0 = X3 ) ),
    inference(superposition,[],[f59,f389])).

fof(f389,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f382,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f382,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f171,f343])).

fof(f343,plain,
    ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f342,f48])).

fof(f48,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f342,plain,
    ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
    | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(equality_resolution,[],[f324])).

fof(f324,plain,(
    ! [X18] :
      ( sK3 != X18
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X18)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,(
    ! [X18] :
      ( sK3 != X18
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X18)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X18)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(superposition,[],[f52,f305])).

fof(f305,plain,(
    ! [X0] :
      ( sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(subsumption_resolution,[],[f304,f111])).

fof(f111,plain,
    ( v1_partfun1(sK3,sK0)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f110,f45])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f102,f46])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | v1_partfun1(sK3,sK0)
    | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f47,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f304,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | ~ v1_partfun1(sK3,sK0)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)
      | ~ v1_partfun1(sK3,sK0)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f196,f204])).

fof(f204,plain,(
    ! [X10] :
      ( v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10)
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f203,f124])).

fof(f124,plain,(
    ! [X0] :
      ( v1_funct_2(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f96,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sK4(X0,X1) != X1
        & r2_hidden(sK4(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK4(X0,X1) != X1
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f96,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | v1_funct_2(X3,sK0,k1_tarski(sK1)) ) ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | v1_funct_2(X3,sK0,k1_tarski(sK1))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f203,plain,(
    ! [X10] :
      ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10)
      | k1_xboole_0 = k1_tarski(sK1)
      | v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0)
      | ~ v1_funct_2(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0,k1_tarski(sK1)) ) ),
    inference(subsumption_resolution,[],[f189,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f95,f51])).

fof(f95,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f87,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | v1_funct_1(X2)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f44,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f189,plain,(
    ! [X10] :
      ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10)
      | k1_xboole_0 = k1_tarski(sK1)
      | v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0)
      | ~ v1_funct_2(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0,k1_tarski(sK1))
      | ~ v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10)) ) ),
    inference(resolution,[],[f130,f83])).

fof(f130,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) ) ),
    inference(resolution,[],[f97,f51])).

fof(f97,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ) ),
    inference(subsumption_resolution,[],[f89,f43])).

fof(f89,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f196,plain,(
    ! [X2] :
      ( ~ v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0)
      | k1_tarski(X2) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2)
      | ~ v1_partfun1(sK3,sK0) ) ),
    inference(subsumption_resolution,[],[f183,f118])).

fof(f183,plain,(
    ! [X2] :
      ( k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | k1_tarski(X2) = k5_partfun1(sK0,k1_tarski(sK1),sK2)
      | ~ v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0)
      | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2)) ) ),
    inference(resolution,[],[f130,f109])).

fof(f109,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_partfun1(X1,sK0)
      | sK3 = X1
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f108,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r1_partfun1(X0,sK3)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f100,f45])).

fof(f100,plain,(
    ! [X0] :
      ( r1_partfun1(X0,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f47,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f108,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK3)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X1,sK0)
      | sK3 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f101,f45])).

fof(f101,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK3)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X1,sK0)
      | sK3 = X1
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f47,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f171,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,k1_tarski(sK1),sK2),k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f170,f48])).

fof(f170,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3)
    | ~ r1_tarski(k5_partfun1(sK0,k1_tarski(sK1),sK2),k1_tarski(sK3)) ),
    inference(resolution,[],[f169,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f169,plain,
    ( r1_tarski(k1_tarski(sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f168,f61])).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f168,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( r1_tarski(k2_tarski(sK3,sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(resolution,[],[f151,f142])).

fof(f142,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f140,f43])).

fof(f140,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2))
    | k1_xboole_0 = k1_tarski(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f117,f44])).

fof(f117,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X5))
      | k1_xboole_0 = k1_tarski(sK1)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f116,f107])).

fof(f116,plain,(
    ! [X5] :
      ( k1_xboole_0 = k1_tarski(sK1)
      | ~ r1_partfun1(X5,sK3)
      | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f115,f45])).

fof(f115,plain,(
    ! [X5] :
      ( k1_xboole_0 = k1_tarski(sK1)
      | ~ r1_partfun1(X5,sK3)
      | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X5))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f106,plain,(
    ! [X5] :
      ( k1_xboole_0 = k1_tarski(sK1)
      | ~ r1_partfun1(X5,sK3)
      | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X5))
      | ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_partfun1(X2,X3)
      | r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

fof(f151,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | r1_tarski(k2_tarski(X0,sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2))
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(resolution,[],[f142,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f628,plain,(
    k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f393,f577])).

fof(f393,plain,(
    k1_tarski(sK3) != k5_partfun1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f48,f389])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (3390)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.49  % (3382)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.23/0.52  % (3380)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.52  % (3369)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.23/0.52  % (3372)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.52  % (3381)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.52  % (3393)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.23/0.52  % (3391)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.52  % (3383)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.52  % (3397)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.23/0.53  % (3392)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.23/0.53  % (3396)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.23/0.53  % (3396)Refutation not found, incomplete strategy% (3396)------------------------------
% 1.23/0.53  % (3396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (3396)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (3396)Memory used [KB]: 6268
% 1.23/0.53  % (3396)Time elapsed: 0.133 s
% 1.23/0.53  % (3396)------------------------------
% 1.23/0.53  % (3396)------------------------------
% 1.23/0.53  % (3373)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.23/0.53  % (3378)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.23/0.53  % (3374)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.53  % (3375)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.53  % (3379)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.53  % (3376)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.53  % (3386)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.54  % (3384)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.54  % (3388)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.54  % (3371)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.54  % (3389)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.54  % (3393)Refutation not found, incomplete strategy% (3393)------------------------------
% 1.39/0.54  % (3393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (3393)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (3393)Memory used [KB]: 10618
% 1.39/0.54  % (3393)Time elapsed: 0.138 s
% 1.39/0.54  % (3393)------------------------------
% 1.39/0.54  % (3393)------------------------------
% 1.39/0.54  % (3398)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.54  % (3387)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.54  % (3398)Refutation not found, incomplete strategy% (3398)------------------------------
% 1.39/0.54  % (3398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (3398)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (3398)Memory used [KB]: 1663
% 1.39/0.54  % (3398)Time elapsed: 0.002 s
% 1.39/0.54  % (3398)------------------------------
% 1.39/0.54  % (3398)------------------------------
% 1.39/0.54  % (3394)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.54  % (3370)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.55  % (3395)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (3385)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.55  % (3385)Refutation not found, incomplete strategy% (3385)------------------------------
% 1.39/0.55  % (3385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (3385)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (3385)Memory used [KB]: 10746
% 1.39/0.55  % (3385)Time elapsed: 0.149 s
% 1.39/0.55  % (3385)------------------------------
% 1.39/0.55  % (3385)------------------------------
% 1.39/0.55  % (3377)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.55  % (3383)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f704,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(subsumption_resolution,[],[f628,f577])).
% 1.39/0.55  fof(f577,plain,(
% 1.39/0.55    ( ! [X3] : (k1_xboole_0 = X3) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f573,f78])).
% 1.39/0.55  fof(f78,plain,(
% 1.39/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f54])).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.55    inference(flattening,[],[f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.55    inference(nnf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.55  fof(f573,plain,(
% 1.39/0.55    ( ! [X3] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X3) | k1_xboole_0 = X3) )),
% 1.39/0.55    inference(superposition,[],[f59,f389])).
% 1.39/0.55  fof(f389,plain,(
% 1.39/0.55    k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f382,f72])).
% 1.39/0.55  fof(f72,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.39/0.55  fof(f382,plain,(
% 1.39/0.55    ~r1_tarski(k1_xboole_0,k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f359])).
% 1.39/0.55  fof(f359,plain,(
% 1.39/0.55    ~r1_tarski(k1_xboole_0,k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.55    inference(superposition,[],[f171,f343])).
% 1.39/0.55  fof(f343,plain,(
% 1.39/0.55    k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f342,f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f33,f32])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f19,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 1.39/0.55    inference(flattening,[],[f18])).
% 1.39/0.55  fof(f18,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f17])).
% 1.39/0.55  fof(f17,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 1.39/0.55    inference(negated_conjecture,[],[f16])).
% 1.39/0.55  fof(f16,conjecture,(
% 1.39/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).
% 1.39/0.55  fof(f342,plain,(
% 1.39/0.55    k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.55    inference(equality_resolution,[],[f324])).
% 1.39/0.55  fof(f324,plain,(
% 1.39/0.55    ( ! [X18] : (sK3 != X18 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X18) | k1_xboole_0 = k1_tarski(sK1)) )),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f323])).
% 1.39/0.55  fof(f323,plain,(
% 1.39/0.55    ( ! [X18] : (sK3 != X18 | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X18) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X18) | k1_xboole_0 = k1_tarski(sK1)) )),
% 1.39/0.55    inference(superposition,[],[f52,f305])).
% 1.39/0.55  fof(f305,plain,(
% 1.39/0.55    ( ! [X0] : (sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f304,f111])).
% 1.39/0.55  fof(f111,plain,(
% 1.39/0.55    v1_partfun1(sK3,sK0) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.55    inference(subsumption_resolution,[],[f110,f45])).
% 1.39/0.55  fof(f45,plain,(
% 1.39/0.55    v1_funct_1(sK3)),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f110,plain,(
% 1.39/0.55    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3)),
% 1.39/0.55    inference(subsumption_resolution,[],[f102,f46])).
% 1.39/0.55  fof(f46,plain,(
% 1.39/0.55    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f102,plain,(
% 1.39/0.55    k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK3,sK0) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3)),
% 1.39/0.55    inference(resolution,[],[f47,f83])).
% 1.39/0.55  fof(f83,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f65])).
% 1.39/0.55  fof(f65,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.39/0.55    inference(flattening,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f304,plain,(
% 1.39/0.55    ( ! [X0] : (k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | ~v1_partfun1(sK3,sK0) | k1_xboole_0 = k1_tarski(sK1)) )),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f303])).
% 1.39/0.55  fof(f303,plain,(
% 1.39/0.55    ( ! [X0] : (k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0) | ~v1_partfun1(sK3,sK0) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 1.39/0.55    inference(resolution,[],[f196,f204])).
% 1.39/0.55  fof(f204,plain,(
% 1.39/0.55    ( ! [X10] : (v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f203,f124])).
% 1.39/0.55  fof(f124,plain,(
% 1.39/0.55    ( ! [X0] : (v1_funct_2(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),sK0,k1_tarski(sK1)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 1.39/0.55    inference(resolution,[],[f96,f51])).
% 1.39/0.55  fof(f51,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ! [X0,X1] : ((sK4(X0,X1) != X1 & r2_hidden(sK4(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f35])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK4(X0,X1) != X1 & r2_hidden(sK4(X0,X1),X0)))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.39/0.55    inference(ennf_transformation,[],[f6])).
% 1.39/0.55  fof(f6,axiom,(
% 1.39/0.55    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.39/0.55  fof(f96,plain,(
% 1.39/0.55    ( ! [X3] : (~r2_hidden(X3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X3,sK0,k1_tarski(sK1))) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f88,f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    v1_funct_1(sK2)),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f88,plain,(
% 1.39/0.55    ( ! [X3] : (~r2_hidden(X3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_2(X3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK2)) )),
% 1.39/0.55    inference(resolution,[],[f44,f63])).
% 1.39/0.55  fof(f63,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_2(X3,X0,X1) | ~v1_funct_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f25])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.39/0.55    inference(flattening,[],[f24])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f15])).
% 1.39/0.55  fof(f15,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) => (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f203,plain,(
% 1.39/0.55    ( ! [X10] : (k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10) | k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0) | ~v1_funct_2(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0,k1_tarski(sK1))) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f189,f118])).
% 1.39/0.55  fof(f118,plain,(
% 1.39/0.55    ( ! [X0] : (v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0)) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 1.39/0.55    inference(resolution,[],[f95,f51])).
% 1.39/0.55  fof(f95,plain,(
% 1.39/0.55    ( ! [X2] : (~r2_hidden(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X2)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f87,f43])).
% 1.39/0.55  fof(f87,plain,(
% 1.39/0.55    ( ! [X2] : (~r2_hidden(X2,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | v1_funct_1(X2) | ~v1_funct_1(sK2)) )),
% 1.39/0.55    inference(resolution,[],[f44,f62])).
% 1.39/0.55  fof(f62,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | v1_funct_1(X3) | ~v1_funct_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f25])).
% 1.39/0.55  fof(f189,plain,(
% 1.39/0.55    ( ! [X10] : (k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(X10) | k1_xboole_0 = k1_tarski(sK1) | v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0) | ~v1_funct_2(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10),sK0,k1_tarski(sK1)) | ~v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X10))) )),
% 1.39/0.55    inference(resolution,[],[f130,f83])).
% 1.39/0.55  fof(f130,plain,(
% 1.39/0.55    ( ! [X0] : (m1_subset_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X0) = k5_partfun1(sK0,k1_tarski(sK1),sK2)) )),
% 1.39/0.55    inference(resolution,[],[f97,f51])).
% 1.39/0.55  fof(f97,plain,(
% 1.39/0.55    ( ! [X4] : (~r2_hidden(X4,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f89,f43])).
% 1.39/0.55  fof(f89,plain,(
% 1.39/0.55    ( ! [X4] : (~r2_hidden(X4,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(sK2)) )),
% 1.39/0.55    inference(resolution,[],[f44,f64])).
% 1.39/0.55  fof(f64,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X3,k5_partfun1(X0,X1,X2)) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f25])).
% 1.39/0.55  fof(f196,plain,(
% 1.39/0.55    ( ! [X2] : (~v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0) | k1_tarski(X2) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2) | ~v1_partfun1(sK3,sK0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f183,f118])).
% 1.39/0.55  fof(f183,plain,(
% 1.39/0.55    ( ! [X2] : (k1_xboole_0 = k5_partfun1(sK0,k1_tarski(sK1),sK2) | k1_tarski(X2) = k5_partfun1(sK0,k1_tarski(sK1),sK2) | ~v1_partfun1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2),sK0) | sK3 = sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2) | ~v1_partfun1(sK3,sK0) | ~v1_funct_1(sK4(k5_partfun1(sK0,k1_tarski(sK1),sK2),X2))) )),
% 1.39/0.55    inference(resolution,[],[f130,f109])).
% 1.39/0.55  fof(f109,plain,(
% 1.39/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~v1_partfun1(sK3,sK0) | ~v1_funct_1(X1)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f108,f107])).
% 1.39/0.55  fof(f107,plain,(
% 1.39/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r1_partfun1(X0,sK3) | ~v1_funct_1(X0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f100,f45])).
% 1.39/0.55  fof(f100,plain,(
% 1.39/0.55    ( ! [X0] : (r1_partfun1(X0,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X0)) )),
% 1.39/0.55    inference(resolution,[],[f47,f67])).
% 1.39/0.55  fof(f67,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(X2,X3) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f29])).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 1.39/0.55    inference(flattening,[],[f28])).
% 1.39/0.55  fof(f28,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f12])).
% 1.39/0.55  fof(f12,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).
% 1.39/0.55  fof(f108,plain,(
% 1.39/0.55    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f101,f45])).
% 1.39/0.55  fof(f101,plain,(
% 1.39/0.55    ( ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X1,sK0) | sK3 = X1 | ~v1_funct_1(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X1)) )),
% 1.39/0.55    inference(resolution,[],[f47,f68])).
% 1.39/0.58  fof(f68,plain,(
% 1.39/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f31])).
% 1.39/0.58  fof(f31,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.39/0.58    inference(flattening,[],[f30])).
% 1.39/0.58  fof(f30,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.39/0.58    inference(ennf_transformation,[],[f13])).
% 1.39/0.58  fof(f13,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 1.39/0.58  fof(f52,plain,(
% 1.39/0.58    ( ! [X0,X1] : (sK4(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.39/0.58    inference(cnf_transformation,[],[f36])).
% 1.39/0.58  fof(f171,plain,(
% 1.39/0.58    ~r1_tarski(k5_partfun1(sK0,k1_tarski(sK1),sK2),k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.58    inference(subsumption_resolution,[],[f170,f48])).
% 1.39/0.58  fof(f170,plain,(
% 1.39/0.58    k1_xboole_0 = k1_tarski(sK1) | k5_partfun1(sK0,k1_tarski(sK1),sK2) = k1_tarski(sK3) | ~r1_tarski(k5_partfun1(sK0,k1_tarski(sK1),sK2),k1_tarski(sK3))),
% 1.39/0.58    inference(resolution,[],[f169,f58])).
% 1.39/0.58  fof(f58,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f40])).
% 1.39/0.58  fof(f40,plain,(
% 1.39/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.58    inference(flattening,[],[f39])).
% 1.39/0.58  fof(f39,plain,(
% 1.39/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.58    inference(nnf_transformation,[],[f1])).
% 1.39/0.58  fof(f1,axiom,(
% 1.39/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.58  fof(f169,plain,(
% 1.39/0.58    r1_tarski(k1_tarski(sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.58    inference(forward_demodulation,[],[f168,f61])).
% 1.39/0.58  fof(f61,plain,(
% 1.39/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f3])).
% 1.39/0.58  fof(f3,axiom,(
% 1.39/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.58  fof(f168,plain,(
% 1.39/0.58    r1_tarski(k2_tarski(sK3,sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.58    inference(duplicate_literal_removal,[],[f165])).
% 1.39/0.58  fof(f165,plain,(
% 1.39/0.58    r1_tarski(k2_tarski(sK3,sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.58    inference(resolution,[],[f151,f142])).
% 1.39/0.58  fof(f142,plain,(
% 1.39/0.58    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1)),
% 1.39/0.58    inference(subsumption_resolution,[],[f140,f43])).
% 1.39/0.58  fof(f140,plain,(
% 1.39/0.58    r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1) | ~v1_funct_1(sK2)),
% 1.39/0.58    inference(resolution,[],[f117,f44])).
% 1.39/0.58  fof(f117,plain,(
% 1.39/0.58    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X5)) | k1_xboole_0 = k1_tarski(sK1) | ~v1_funct_1(X5)) )),
% 1.39/0.58    inference(subsumption_resolution,[],[f116,f107])).
% 1.39/0.58  fof(f116,plain,(
% 1.39/0.58    ( ! [X5] : (k1_xboole_0 = k1_tarski(sK1) | ~r1_partfun1(X5,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X5)) )),
% 1.39/0.58    inference(subsumption_resolution,[],[f115,f45])).
% 1.39/0.58  fof(f115,plain,(
% 1.39/0.58    ( ! [X5] : (k1_xboole_0 = k1_tarski(sK1) | ~r1_partfun1(X5,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X5)) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X5)) )),
% 1.39/0.58    inference(subsumption_resolution,[],[f106,f46])).
% 1.39/0.58  fof(f106,plain,(
% 1.39/0.58    ( ! [X5] : (k1_xboole_0 = k1_tarski(sK1) | ~r1_partfun1(X5,sK3) | r2_hidden(sK3,k5_partfun1(sK0,k1_tarski(sK1),X5)) | ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_1(X5)) )),
% 1.39/0.58    inference(resolution,[],[f47,f49])).
% 1.39/0.58  fof(f49,plain,(
% 1.39/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_partfun1(X2,X3) | r2_hidden(X3,k5_partfun1(X0,X1,X2)) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f21])).
% 1.39/0.58  fof(f21,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (! [X3] : (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.39/0.58    inference(flattening,[],[f20])).
% 1.39/0.58  fof(f20,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (! [X3] : (((r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_partfun1(X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.39/0.58    inference(ennf_transformation,[],[f14])).
% 1.39/0.58  fof(f14,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).
% 1.39/0.58  fof(f151,plain,(
% 1.39/0.58    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,k1_tarski(sK1),sK2)) | r1_tarski(k2_tarski(X0,sK3),k5_partfun1(sK0,k1_tarski(sK1),sK2)) | k1_xboole_0 = k1_tarski(sK1)) )),
% 1.39/0.58    inference(resolution,[],[f142,f71])).
% 1.39/0.58  fof(f71,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f42])).
% 1.39/0.58  fof(f42,plain,(
% 1.39/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.39/0.58    inference(flattening,[],[f41])).
% 1.39/0.58  fof(f41,plain,(
% 1.39/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.39/0.58    inference(nnf_transformation,[],[f10])).
% 1.39/0.58  fof(f10,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.39/0.58  fof(f59,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 1.39/0.58    inference(cnf_transformation,[],[f23])).
% 1.39/0.58  fof(f23,plain,(
% 1.39/0.58    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 1.39/0.58    inference(ennf_transformation,[],[f8])).
% 1.39/0.58  fof(f8,axiom,(
% 1.39/0.58    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 1.39/0.58  fof(f628,plain,(
% 1.39/0.58    k1_xboole_0 != k5_partfun1(sK0,k1_xboole_0,sK2)),
% 1.39/0.58    inference(backward_demodulation,[],[f393,f577])).
% 1.39/0.58  fof(f393,plain,(
% 1.39/0.58    k1_tarski(sK3) != k5_partfun1(sK0,k1_xboole_0,sK2)),
% 1.39/0.58    inference(backward_demodulation,[],[f48,f389])).
% 1.39/0.58  % SZS output end Proof for theBenchmark
% 1.39/0.58  % (3383)------------------------------
% 1.39/0.58  % (3383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (3383)Termination reason: Refutation
% 1.39/0.58  
% 1.39/0.58  % (3383)Memory used [KB]: 2046
% 1.39/0.58  % (3383)Time elapsed: 0.109 s
% 1.39/0.58  % (3383)------------------------------
% 1.39/0.58  % (3383)------------------------------
% 1.39/0.58  % (3368)Success in time 0.224 s
%------------------------------------------------------------------------------
