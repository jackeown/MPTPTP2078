%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:01 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  104 (1096 expanded)
%              Number of leaves         :   16 ( 352 expanded)
%              Depth                    :   27
%              Number of atoms          :  545 (7594 expanded)
%              Number of equality atoms :  164 (1618 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f696,plain,(
    $false ),
    inference(subsumption_resolution,[],[f620,f593])).

fof(f593,plain,(
    ! [X0] : k1_xboole_0 = X0 ),
    inference(subsumption_resolution,[],[f588,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f588,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f74,f401])).

fof(f401,plain,(
    k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f400,f163])).

fof(f163,plain,
    ( r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(resolution,[],[f135,f109])).

fof(f109,plain,
    ( v1_partfun1(sK5,sK2)
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f108,f45])).

fof(f45,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
          & v1_funct_2(X3,sK2,k1_tarski(sK3))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
        & v1_funct_2(X3,sK2,k1_tarski(sK3))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(f108,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | v1_partfun1(sK5,sK2)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f103,f46])).

fof(f46,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | v1_partfun1(sK5,sK2)
    | ~ v1_funct_2(sK5,sK2,k1_tarski(sK3))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f47,f89])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f135,plain,
    ( ~ v1_partfun1(sK5,sK2)
    | r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f131,f127])).

fof(f127,plain,(
    r1_partfun1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f123,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f123,plain,
    ( r1_partfun1(sK4,sK5)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f107,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | r1_partfun1(X0,sK5)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f102,plain,(
    ! [X0] :
      ( r1_partfun1(X0,sK5)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f47,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | r1_partfun1(X2,X3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(f131,plain,
    ( ~ v1_partfun1(sK5,sK2)
    | r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | ~ r1_partfun1(sK4,sK5) ),
    inference(resolution,[],[f101,f113])).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ sP0(X2,sK2,k1_tarski(sK3),X3)
      | ~ v1_partfun1(sK5,sK2)
      | r2_hidden(sK5,X3)
      | ~ r1_partfun1(X2,sK5) ) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f106,plain,(
    ! [X2,X3] :
      ( ~ r1_partfun1(X2,sK5)
      | ~ v1_partfun1(sK5,sK2)
      | r2_hidden(sK5,X3)
      | ~ v1_funct_1(sK5)
      | ~ sP0(X2,sK2,k1_tarski(sK3),X3) ) ),
    inference(resolution,[],[f47,f81])).

fof(f81,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | r2_hidden(X8,X3)
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK6(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
              & v1_partfun1(sK7(X0,X1,X2,X3),X1)
              & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3)
              & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK7(X0,X1,X2,X3)) )
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK8(X0,X1,X2,X7))
                & v1_partfun1(sK8(X0,X1,X2,X7),X1)
                & sK8(X0,X1,X2,X7) = X7
                & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK8(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK6(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK6(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & sK6(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK7(X0,X1,X2,X3))
        & v1_partfun1(sK7(X0,X1,X2,X3),X1)
        & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK7(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK8(X0,X1,X2,X7))
        & v1_partfun1(sK8(X0,X1,X2,X7),X1)
        & sK8(X0,X1,X2,X7) = X7
        & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK8(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f101,plain,(
    sP0(sK4,sK2,k1_tarski(sK3),k5_partfun1(sK2,k1_tarski(sK3),sK4)) ),
    inference(resolution,[],[f99,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f99,plain,(
    sP1(k1_tarski(sK3),sK2,sK4) ),
    inference(subsumption_resolution,[],[f93,f43])).

fof(f93,plain,
    ( sP1(k1_tarski(sK3),sK2,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X1,X0,X2)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f15,f24,f23])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(f400,plain,
    ( ~ r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f399,f48])).

fof(f48,plain,(
    k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f399,plain,
    ( k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5)
    | ~ r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(trivial_inequality_removal,[],[f398])).

fof(f398,plain,
    ( sK5 != sK5
    | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5)
    | ~ r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(superposition,[],[f73,f385])).

fof(f385,plain,
    ( sK5 = sK9(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(subsumption_resolution,[],[f384,f48])).

fof(f384,plain,
    ( sK5 = sK9(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))
    | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5)
    | k1_xboole_0 = k1_tarski(sK3) ),
    inference(equality_resolution,[],[f365])).

fof(f365,plain,(
    ! [X0] :
      ( sK5 != X0
      | sK5 = sK9(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_xboole_0 = k1_tarski(sK3) ) ),
    inference(equality_factoring,[],[f347])).

fof(f347,plain,(
    ! [X1] :
      ( sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X1
      | sK5 = sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_xboole_0 = k1_tarski(sK3) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X1] :
      ( sK5 = sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X1
      | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_xboole_0 = k1_tarski(sK3)
      | sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X1
      | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4) ) ),
    inference(superposition,[],[f228,f172])).

fof(f172,plain,(
    ! [X3] :
      ( sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = sK8(sK4,sK2,k1_tarski(sK3),sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)))
      | sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X3
      | k1_tarski(X3) = k5_partfun1(sK2,k1_tarski(sK3),sK4) ) ),
    inference(resolution,[],[f133,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | sK9(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f133,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | sK8(sK4,sK2,k1_tarski(sK3),X0) = X0 ) ),
    inference(resolution,[],[f101,f53])).

fof(f53,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r2_hidden(X7,X3)
      | sK8(X0,X1,X2,X7) = X7 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f228,plain,(
    ! [X0] :
      ( sK5 = sK8(sK4,sK2,k1_tarski(sK3),sK9(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4)))
      | sK9(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X0
      | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4)
      | k1_xboole_0 = k1_tarski(sK3) ) ),
    inference(resolution,[],[f196,f109])).

fof(f196,plain,(
    ! [X3] :
      ( ~ v1_partfun1(sK5,sK2)
      | sK5 = sK8(sK4,sK2,k1_tarski(sK3),sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)))
      | sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X3
      | k1_tarski(X3) = k5_partfun1(sK2,k1_tarski(sK3),sK4) ) ),
    inference(resolution,[],[f166,f72])).

fof(f166,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4))
      | ~ v1_partfun1(sK5,sK2)
      | sK5 = sK8(sK4,sK2,k1_tarski(sK3),X0) ) ),
    inference(resolution,[],[f156,f101])).

fof(f156,plain,(
    ! [X4,X2,X3] :
      ( ~ sP0(X2,sK2,k1_tarski(sK3),X4)
      | ~ v1_partfun1(sK5,sK2)
      | ~ r2_hidden(X3,X4)
      | sK5 = sK8(X2,sK2,k1_tarski(sK3),X3) ) ),
    inference(subsumption_resolution,[],[f155,f51])).

fof(f51,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_funct_1(sK8(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f155,plain,(
    ! [X4,X2,X3] :
      ( sK5 = sK8(X2,sK2,k1_tarski(sK3),X3)
      | ~ v1_partfun1(sK5,sK2)
      | ~ v1_funct_1(sK8(X2,sK2,k1_tarski(sK3),X3))
      | ~ r2_hidden(X3,X4)
      | ~ sP0(X2,sK2,k1_tarski(sK3),X4) ) ),
    inference(subsumption_resolution,[],[f151,f54])).

fof(f54,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK8(X0,X1,X2,X7),X1)
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f151,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_partfun1(sK8(X2,sK2,k1_tarski(sK3),X3),sK2)
      | sK5 = sK8(X2,sK2,k1_tarski(sK3),X3)
      | ~ v1_partfun1(sK5,sK2)
      | ~ v1_funct_1(sK8(X2,sK2,k1_tarski(sK3),X3))
      | ~ r2_hidden(X3,X4)
      | ~ sP0(X2,sK2,k1_tarski(sK3),X4) ) ),
    inference(resolution,[],[f111,f52])).

fof(f52,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_partfun1(X1,sK2)
      | sK5 = X1
      | ~ v1_partfun1(sK5,sK2)
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f110,f107])).

fof(f110,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK5)
      | ~ v1_partfun1(sK5,sK2)
      | ~ v1_partfun1(X1,sK2)
      | sK5 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK5)
      | ~ v1_partfun1(sK5,sK2)
      | ~ v1_partfun1(X1,sK2)
      | sK5 = X1
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f47,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f73,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f620,plain,(
    k1_xboole_0 != k5_partfun1(sK2,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f405,f593])).

fof(f405,plain,(
    k1_tarski(sK5) != k5_partfun1(sK2,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f48,f401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (16463)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (16460)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (16452)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (16450)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (16437)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.26/0.52  % (16466)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.52  % (16447)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.26/0.52  % (16444)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.52  % (16455)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.26/0.53  % (16439)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.53  % (16458)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.26/0.53  % (16438)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.53  % (16465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.26/0.53  % (16464)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.26/0.53  % (16440)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.53  % (16442)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.54  % (16441)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.41/0.54  % (16461)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.54  % (16454)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.54  % (16453)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.54  % (16451)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.54  % (16457)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.54  % (16456)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.54  % (16446)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.55  % (16445)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.55  % (16448)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.55  % (16449)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.55  % (16461)Refutation not found, incomplete strategy% (16461)------------------------------
% 1.41/0.55  % (16461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (16461)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (16461)Memory used [KB]: 10746
% 1.41/0.55  % (16461)Time elapsed: 0.139 s
% 1.41/0.55  % (16461)------------------------------
% 1.41/0.55  % (16461)------------------------------
% 1.41/0.56  % (16462)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.56  % (16453)Refutation not found, incomplete strategy% (16453)------------------------------
% 1.41/0.56  % (16453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (16453)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (16453)Memory used [KB]: 10746
% 1.41/0.56  % (16453)Time elapsed: 0.151 s
% 1.41/0.56  % (16453)------------------------------
% 1.41/0.56  % (16453)------------------------------
% 1.41/0.58  % (16443)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.59  % (16459)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.41/0.62  % (16451)Refutation found. Thanks to Tanya!
% 1.41/0.62  % SZS status Theorem for theBenchmark
% 1.41/0.62  % SZS output start Proof for theBenchmark
% 1.41/0.62  fof(f696,plain,(
% 1.41/0.62    $false),
% 1.41/0.62    inference(subsumption_resolution,[],[f620,f593])).
% 1.41/0.62  fof(f593,plain,(
% 1.41/0.62    ( ! [X0] : (k1_xboole_0 = X0) )),
% 1.41/0.62    inference(subsumption_resolution,[],[f588,f84])).
% 1.41/0.62  fof(f84,plain,(
% 1.41/0.62    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.41/0.62    inference(equality_resolution,[],[f68])).
% 1.41/0.62  fof(f68,plain,(
% 1.41/0.62    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.41/0.62    inference(cnf_transformation,[],[f38])).
% 1.41/0.62  fof(f38,plain,(
% 1.41/0.62    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.41/0.62    inference(flattening,[],[f37])).
% 2.10/0.63  fof(f37,plain,(
% 2.10/0.63    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.10/0.63    inference(nnf_transformation,[],[f4])).
% 2.10/0.63  fof(f4,axiom,(
% 2.10/0.63    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.10/0.63  fof(f588,plain,(
% 2.10/0.63    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 2.10/0.63    inference(superposition,[],[f74,f401])).
% 2.10/0.63  fof(f401,plain,(
% 2.10/0.63    k1_xboole_0 = k1_tarski(sK3)),
% 2.10/0.63    inference(subsumption_resolution,[],[f400,f163])).
% 2.10/0.63  fof(f163,plain,(
% 2.10/0.63    r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)),
% 2.10/0.63    inference(resolution,[],[f135,f109])).
% 2.10/0.63  fof(f109,plain,(
% 2.10/0.63    v1_partfun1(sK5,sK2) | k1_xboole_0 = k1_tarski(sK3)),
% 2.10/0.63    inference(subsumption_resolution,[],[f108,f45])).
% 2.10/0.63  fof(f45,plain,(
% 2.10/0.63    v1_funct_1(sK5)),
% 2.10/0.63    inference(cnf_transformation,[],[f28])).
% 2.10/0.63  fof(f28,plain,(
% 2.10/0.63    (k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_1(sK4)),
% 2.10/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f27,f26])).
% 2.10/0.63  fof(f26,plain,(
% 2.10/0.63    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(X3,sK2,k1_tarski(sK3)) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_1(sK4))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f27,plain,(
% 2.10/0.63    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK2,k1_tarski(sK3),sK4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(X3,sK2,k1_tarski(sK3)) & v1_funct_1(X3)) => (k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f13,plain,(
% 2.10/0.63    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 2.10/0.63    inference(flattening,[],[f12])).
% 2.10/0.63  fof(f12,plain,(
% 2.10/0.63    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 2.10/0.63    inference(ennf_transformation,[],[f11])).
% 2.10/0.63  fof(f11,negated_conjecture,(
% 2.10/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 2.10/0.63    inference(negated_conjecture,[],[f10])).
% 2.10/0.63  fof(f10,conjecture,(
% 2.10/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).
% 2.10/0.63  fof(f108,plain,(
% 2.10/0.63    k1_xboole_0 = k1_tarski(sK3) | v1_partfun1(sK5,sK2) | ~v1_funct_1(sK5)),
% 2.10/0.63    inference(subsumption_resolution,[],[f103,f46])).
% 2.10/0.63  fof(f46,plain,(
% 2.10/0.63    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 2.10/0.63    inference(cnf_transformation,[],[f28])).
% 2.10/0.63  fof(f103,plain,(
% 2.10/0.63    k1_xboole_0 = k1_tarski(sK3) | v1_partfun1(sK5,sK2) | ~v1_funct_2(sK5,sK2,k1_tarski(sK3)) | ~v1_funct_1(sK5)),
% 2.10/0.63    inference(resolution,[],[f47,f89])).
% 2.10/0.63  fof(f89,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.10/0.63    inference(duplicate_literal_removal,[],[f65])).
% 2.10/0.63  fof(f65,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f19])).
% 2.10/0.63  fof(f19,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.10/0.63    inference(flattening,[],[f18])).
% 2.10/0.63  fof(f18,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.10/0.63    inference(ennf_transformation,[],[f7])).
% 2.10/0.63  fof(f7,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 2.10/0.63  fof(f47,plain,(
% 2.10/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 2.10/0.63    inference(cnf_transformation,[],[f28])).
% 2.10/0.63  fof(f135,plain,(
% 2.10/0.63    ~v1_partfun1(sK5,sK2) | r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4))),
% 2.10/0.63    inference(subsumption_resolution,[],[f131,f127])).
% 2.10/0.63  fof(f127,plain,(
% 2.10/0.63    r1_partfun1(sK4,sK5)),
% 2.10/0.63    inference(subsumption_resolution,[],[f123,f43])).
% 2.10/0.63  fof(f43,plain,(
% 2.10/0.63    v1_funct_1(sK4)),
% 2.10/0.63    inference(cnf_transformation,[],[f28])).
% 2.10/0.63  fof(f123,plain,(
% 2.10/0.63    r1_partfun1(sK4,sK5) | ~v1_funct_1(sK4)),
% 2.10/0.63    inference(resolution,[],[f107,f44])).
% 2.10/0.63  fof(f44,plain,(
% 2.10/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 2.10/0.63    inference(cnf_transformation,[],[f28])).
% 2.10/0.63  fof(f107,plain,(
% 2.10/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | r1_partfun1(X0,sK5) | ~v1_funct_1(X0)) )),
% 2.10/0.63    inference(subsumption_resolution,[],[f102,f45])).
% 2.10/0.63  fof(f102,plain,(
% 2.10/0.63    ( ! [X0] : (r1_partfun1(X0,sK5) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_funct_1(X0)) )),
% 2.10/0.63    inference(resolution,[],[f47,f77])).
% 2.10/0.63  fof(f77,plain,(
% 2.10/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | r1_partfun1(X2,X3) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f22])).
% 2.10/0.63  fof(f22,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 2.10/0.63    inference(flattening,[],[f21])).
% 2.10/0.63  fof(f21,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 2.10/0.63    inference(ennf_transformation,[],[f8])).
% 2.10/0.63  fof(f8,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).
% 2.10/0.63  fof(f131,plain,(
% 2.10/0.63    ~v1_partfun1(sK5,sK2) | r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | ~r1_partfun1(sK4,sK5)),
% 2.10/0.63    inference(resolution,[],[f101,f113])).
% 2.10/0.63  fof(f113,plain,(
% 2.10/0.63    ( ! [X2,X3] : (~sP0(X2,sK2,k1_tarski(sK3),X3) | ~v1_partfun1(sK5,sK2) | r2_hidden(sK5,X3) | ~r1_partfun1(X2,sK5)) )),
% 2.10/0.63    inference(subsumption_resolution,[],[f106,f45])).
% 2.10/0.63  fof(f106,plain,(
% 2.10/0.63    ( ! [X2,X3] : (~r1_partfun1(X2,sK5) | ~v1_partfun1(sK5,sK2) | r2_hidden(sK5,X3) | ~v1_funct_1(sK5) | ~sP0(X2,sK2,k1_tarski(sK3),X3)) )),
% 2.10/0.63    inference(resolution,[],[f47,f81])).
% 2.10/0.63  fof(f81,plain,(
% 2.10/0.63    ( ! [X2,X0,X8,X3,X1] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | r2_hidden(X8,X3) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.10/0.63    inference(equality_resolution,[],[f56])).
% 2.10/0.63  fof(f56,plain,(
% 2.10/0.63    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f36])).
% 2.10/0.63  fof(f36,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK6(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X1) & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3) & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK7(X0,X1,X2,X3))) | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK8(X0,X1,X2,X7)) & v1_partfun1(sK8(X0,X1,X2,X7),X1) & sK8(X0,X1,X2,X7) = X7 & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK8(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.10/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f32,f35,f34,f33])).
% 2.10/0.63  fof(f33,plain,(
% 2.10/0.63    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK6(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK6(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f34,plain,(
% 2.10/0.63    ! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK6(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK7(X0,X1,X2,X3)) & v1_partfun1(sK7(X0,X1,X2,X3),X1) & sK6(X0,X1,X2,X3) = sK7(X0,X1,X2,X3) & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK7(X0,X1,X2,X3))))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f35,plain,(
% 2.10/0.63    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK8(X0,X1,X2,X7)) & v1_partfun1(sK8(X0,X1,X2,X7),X1) & sK8(X0,X1,X2,X7) = X7 & m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK8(X0,X1,X2,X7))))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f32,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.10/0.63    inference(rectify,[],[f31])).
% 2.10/0.63  fof(f31,plain,(
% 2.10/0.63    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 2.10/0.63    inference(nnf_transformation,[],[f23])).
% 2.10/0.63  fof(f23,plain,(
% 2.10/0.63    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 2.10/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.10/0.63  fof(f101,plain,(
% 2.10/0.63    sP0(sK4,sK2,k1_tarski(sK3),k5_partfun1(sK2,k1_tarski(sK3),sK4))),
% 2.10/0.63    inference(resolution,[],[f99,f79])).
% 2.10/0.63  fof(f79,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))) )),
% 2.10/0.63    inference(equality_resolution,[],[f49])).
% 2.10/0.63  fof(f49,plain,(
% 2.10/0.63    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f30])).
% 2.10/0.64  fof(f30,plain,(
% 2.10/0.64    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 2.10/0.64    inference(rectify,[],[f29])).
% 2.10/0.64  fof(f29,plain,(
% 2.10/0.64    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 2.10/0.64    inference(nnf_transformation,[],[f24])).
% 2.10/0.64  fof(f24,plain,(
% 2.10/0.64    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 2.10/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.10/0.64  fof(f99,plain,(
% 2.10/0.64    sP1(k1_tarski(sK3),sK2,sK4)),
% 2.10/0.64    inference(subsumption_resolution,[],[f93,f43])).
% 2.10/0.64  fof(f93,plain,(
% 2.10/0.64    sP1(k1_tarski(sK3),sK2,sK4) | ~v1_funct_1(sK4)),
% 2.10/0.64    inference(resolution,[],[f44,f63])).
% 2.10/0.64  fof(f63,plain,(
% 2.10/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X1,X0,X2) | ~v1_funct_1(X2)) )),
% 2.10/0.64    inference(cnf_transformation,[],[f25])).
% 2.10/0.64  fof(f25,plain,(
% 2.10/0.64    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.10/0.64    inference(definition_folding,[],[f15,f24,f23])).
% 2.10/0.64  fof(f15,plain,(
% 2.10/0.64    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.10/0.64    inference(flattening,[],[f14])).
% 2.10/0.64  fof(f14,plain,(
% 2.10/0.64    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.10/0.64    inference(ennf_transformation,[],[f6])).
% 2.10/0.64  fof(f6,axiom,(
% 2.10/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 2.10/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).
% 2.10/0.64  fof(f400,plain,(
% 2.10/0.64    ~r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)),
% 2.10/0.64    inference(subsumption_resolution,[],[f399,f48])).
% 2.10/0.64  fof(f48,plain,(
% 2.10/0.64    k5_partfun1(sK2,k1_tarski(sK3),sK4) != k1_tarski(sK5)),
% 2.10/0.64    inference(cnf_transformation,[],[f28])).
% 2.10/0.64  fof(f399,plain,(
% 2.10/0.64    k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5) | ~r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)),
% 2.10/0.64    inference(trivial_inequality_removal,[],[f398])).
% 2.10/0.64  fof(f398,plain,(
% 2.10/0.64    sK5 != sK5 | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5) | ~r2_hidden(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)),
% 2.10/0.64    inference(superposition,[],[f73,f385])).
% 2.10/0.64  fof(f385,plain,(
% 2.10/0.64    sK5 = sK9(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_xboole_0 = k1_tarski(sK3)),
% 2.10/0.64    inference(subsumption_resolution,[],[f384,f48])).
% 2.10/0.64  fof(f384,plain,(
% 2.10/0.64    sK5 = sK9(sK5,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k5_partfun1(sK2,k1_tarski(sK3),sK4) = k1_tarski(sK5) | k1_xboole_0 = k1_tarski(sK3)),
% 2.10/0.64    inference(equality_resolution,[],[f365])).
% 2.10/0.64  fof(f365,plain,(
% 2.10/0.64    ( ! [X0] : (sK5 != X0 | sK5 = sK9(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_xboole_0 = k1_tarski(sK3)) )),
% 2.10/0.64    inference(equality_factoring,[],[f347])).
% 2.10/0.64  fof(f347,plain,(
% 2.10/0.64    ( ! [X1] : (sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X1 | sK5 = sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_xboole_0 = k1_tarski(sK3)) )),
% 2.10/0.64    inference(duplicate_literal_removal,[],[f338])).
% 2.10/0.64  fof(f338,plain,(
% 2.10/0.64    ( ! [X1] : (sK5 = sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X1 | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_xboole_0 = k1_tarski(sK3) | sK9(X1,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X1 | k1_tarski(X1) = k5_partfun1(sK2,k1_tarski(sK3),sK4)) )),
% 2.10/0.64    inference(superposition,[],[f228,f172])).
% 2.10/0.64  fof(f172,plain,(
% 2.10/0.64    ( ! [X3] : (sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = sK8(sK4,sK2,k1_tarski(sK3),sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4))) | sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X3 | k1_tarski(X3) = k5_partfun1(sK2,k1_tarski(sK3),sK4)) )),
% 2.10/0.64    inference(resolution,[],[f133,f72])).
% 2.10/0.64  fof(f72,plain,(
% 2.10/0.64    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | sK9(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 2.10/0.64    inference(cnf_transformation,[],[f42])).
% 2.10/0.64  fof(f42,plain,(
% 2.10/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.10/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f40,f41])).
% 2.10/0.64  fof(f41,plain,(
% 2.10/0.64    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 2.10/0.64    introduced(choice_axiom,[])).
% 2.10/0.64  fof(f40,plain,(
% 2.10/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.10/0.64    inference(rectify,[],[f39])).
% 2.10/0.64  fof(f39,plain,(
% 2.10/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.10/0.64    inference(nnf_transformation,[],[f1])).
% 2.10/0.64  fof(f1,axiom,(
% 2.10/0.64    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.10/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.10/0.64  fof(f133,plain,(
% 2.10/0.64    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | sK8(sK4,sK2,k1_tarski(sK3),X0) = X0) )),
% 2.10/0.64    inference(resolution,[],[f101,f53])).
% 2.10/0.64  fof(f53,plain,(
% 2.10/0.64    ( ! [X2,X0,X7,X3,X1] : (~sP0(X0,X1,X2,X3) | ~r2_hidden(X7,X3) | sK8(X0,X1,X2,X7) = X7) )),
% 2.10/0.64    inference(cnf_transformation,[],[f36])).
% 2.10/0.64  fof(f228,plain,(
% 2.10/0.64    ( ! [X0] : (sK5 = sK8(sK4,sK2,k1_tarski(sK3),sK9(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4))) | sK9(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X0 | k1_tarski(X0) = k5_partfun1(sK2,k1_tarski(sK3),sK4) | k1_xboole_0 = k1_tarski(sK3)) )),
% 2.10/0.64    inference(resolution,[],[f196,f109])).
% 2.10/0.64  fof(f196,plain,(
% 2.10/0.64    ( ! [X3] : (~v1_partfun1(sK5,sK2) | sK5 = sK8(sK4,sK2,k1_tarski(sK3),sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4))) | sK9(X3,k5_partfun1(sK2,k1_tarski(sK3),sK4)) = X3 | k1_tarski(X3) = k5_partfun1(sK2,k1_tarski(sK3),sK4)) )),
% 2.10/0.64    inference(resolution,[],[f166,f72])).
% 2.10/0.64  fof(f166,plain,(
% 2.10/0.64    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK2,k1_tarski(sK3),sK4)) | ~v1_partfun1(sK5,sK2) | sK5 = sK8(sK4,sK2,k1_tarski(sK3),X0)) )),
% 2.10/0.64    inference(resolution,[],[f156,f101])).
% 2.10/0.64  fof(f156,plain,(
% 2.10/0.64    ( ! [X4,X2,X3] : (~sP0(X2,sK2,k1_tarski(sK3),X4) | ~v1_partfun1(sK5,sK2) | ~r2_hidden(X3,X4) | sK5 = sK8(X2,sK2,k1_tarski(sK3),X3)) )),
% 2.10/0.64    inference(subsumption_resolution,[],[f155,f51])).
% 2.10/0.64  fof(f51,plain,(
% 2.10/0.64    ( ! [X2,X0,X7,X3,X1] : (v1_funct_1(sK8(X0,X1,X2,X7)) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 2.10/0.64    inference(cnf_transformation,[],[f36])).
% 2.10/0.64  fof(f155,plain,(
% 2.10/0.64    ( ! [X4,X2,X3] : (sK5 = sK8(X2,sK2,k1_tarski(sK3),X3) | ~v1_partfun1(sK5,sK2) | ~v1_funct_1(sK8(X2,sK2,k1_tarski(sK3),X3)) | ~r2_hidden(X3,X4) | ~sP0(X2,sK2,k1_tarski(sK3),X4)) )),
% 2.10/0.64    inference(subsumption_resolution,[],[f151,f54])).
% 2.10/0.64  fof(f54,plain,(
% 2.10/0.64    ( ! [X2,X0,X7,X3,X1] : (v1_partfun1(sK8(X0,X1,X2,X7),X1) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 2.10/0.64    inference(cnf_transformation,[],[f36])).
% 2.10/0.64  fof(f151,plain,(
% 2.10/0.64    ( ! [X4,X2,X3] : (~v1_partfun1(sK8(X2,sK2,k1_tarski(sK3),X3),sK2) | sK5 = sK8(X2,sK2,k1_tarski(sK3),X3) | ~v1_partfun1(sK5,sK2) | ~v1_funct_1(sK8(X2,sK2,k1_tarski(sK3),X3)) | ~r2_hidden(X3,X4) | ~sP0(X2,sK2,k1_tarski(sK3),X4)) )),
% 2.10/0.64    inference(resolution,[],[f111,f52])).
% 2.10/0.64  fof(f52,plain,(
% 2.10/0.64    ( ! [X2,X0,X7,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X7,X3) | ~sP0(X0,X1,X2,X3)) )),
% 2.10/0.64    inference(cnf_transformation,[],[f36])).
% 2.10/0.64  fof(f111,plain,(
% 2.10/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_partfun1(X1,sK2) | sK5 = X1 | ~v1_partfun1(sK5,sK2) | ~v1_funct_1(X1)) )),
% 2.10/0.64    inference(subsumption_resolution,[],[f110,f107])).
% 2.10/0.64  fof(f110,plain,(
% 2.10/0.64    ( ! [X1] : (~r1_partfun1(X1,sK5) | ~v1_partfun1(sK5,sK2) | ~v1_partfun1(X1,sK2) | sK5 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_funct_1(X1)) )),
% 2.10/0.64    inference(subsumption_resolution,[],[f104,f45])).
% 2.10/0.64  fof(f104,plain,(
% 2.10/0.64    ( ! [X1] : (~r1_partfun1(X1,sK5) | ~v1_partfun1(sK5,sK2) | ~v1_partfun1(X1,sK2) | sK5 = X1 | ~v1_funct_1(sK5) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) | ~v1_funct_1(X1)) )),
% 2.10/0.64    inference(resolution,[],[f47,f64])).
% 2.10/0.64  fof(f64,plain,(
% 2.10/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.10/0.64    inference(cnf_transformation,[],[f17])).
% 2.10/0.64  fof(f17,plain,(
% 2.10/0.64    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.10/0.64    inference(flattening,[],[f16])).
% 2.10/0.64  fof(f16,plain,(
% 2.10/0.64    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.10/0.64    inference(ennf_transformation,[],[f9])).
% 2.10/0.64  fof(f9,axiom,(
% 2.10/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 2.10/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 2.10/0.64  fof(f73,plain,(
% 2.10/0.64    ( ! [X0,X1] : (sK9(X0,X1) != X0 | k1_tarski(X0) = X1 | ~r2_hidden(sK9(X0,X1),X1)) )),
% 2.10/0.64    inference(cnf_transformation,[],[f42])).
% 2.10/0.64  fof(f74,plain,(
% 2.10/0.64    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 2.10/0.64    inference(cnf_transformation,[],[f20])).
% 2.10/0.64  fof(f20,plain,(
% 2.10/0.64    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 2.10/0.64    inference(ennf_transformation,[],[f5])).
% 2.10/0.64  fof(f5,axiom,(
% 2.10/0.64    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 2.10/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 2.10/0.64  fof(f620,plain,(
% 2.10/0.64    k1_xboole_0 != k5_partfun1(sK2,k1_xboole_0,sK4)),
% 2.10/0.64    inference(backward_demodulation,[],[f405,f593])).
% 2.10/0.64  fof(f405,plain,(
% 2.10/0.64    k1_tarski(sK5) != k5_partfun1(sK2,k1_xboole_0,sK4)),
% 2.10/0.64    inference(backward_demodulation,[],[f48,f401])).
% 2.10/0.64  % SZS output end Proof for theBenchmark
% 2.10/0.64  % (16451)------------------------------
% 2.10/0.64  % (16451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.64  % (16451)Termination reason: Refutation
% 2.10/0.64  
% 2.10/0.64  % (16451)Memory used [KB]: 2174
% 2.10/0.64  % (16451)Time elapsed: 0.190 s
% 2.10/0.64  % (16451)------------------------------
% 2.10/0.64  % (16451)------------------------------
% 2.10/0.64  % (16436)Success in time 0.279 s
%------------------------------------------------------------------------------
