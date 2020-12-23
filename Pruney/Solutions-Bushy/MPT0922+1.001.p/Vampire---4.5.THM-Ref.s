%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0922+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:54 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   44 (  80 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   21
%              Number of atoms          :  233 ( 737 expanded)
%              Number of equality atoms :  121 ( 415 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(subsumption_resolution,[],[f43,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X9
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k11_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X9 ) ) ) ) )
         => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X9 ) ) ) ) )
       => ( k11_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_mcart_1)).

fof(f43,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f42,f17])).

fof(f17,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,
    ( ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f41,f23])).

fof(f23,plain,(
    sK4 != k11_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,
    ( sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f40])).

fof(f40,plain,
    ( sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k10_mcart_1(sK0,sK1,X0,sK3,sK5),sK2)
      | sK4 = k11_mcart_1(sK0,sK1,X0,sK3,sK5)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,X0,sK3))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f38,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( sK4 = k11_mcart_1(sK0,sK1,X0,sK3,sK5)
      | ~ m1_subset_1(k10_mcart_1(sK0,sK1,X0,sK3,sK5),sK2)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,X0,sK3))
      | k1_xboole_0 = sK3
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( sK4 = k11_mcart_1(sK0,sK1,X0,sK3,sK5)
      | ~ m1_subset_1(k10_mcart_1(sK0,sK1,X0,sK3,sK5),sK2)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,X0,sK3))
      | k1_xboole_0 = sK3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,X0,sK3)) ) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k11_mcart_1(sK0,sK1,X0,X1,sK5),sK3)
      | sK4 = k11_mcart_1(sK0,sK1,X0,X1,sK5)
      | ~ m1_subset_1(k10_mcart_1(sK0,sK1,X0,X1,sK5),sK2)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f35,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k10_mcart_1(sK0,sK1,X0,X1,sK5),sK2)
      | sK4 = k11_mcart_1(sK0,sK1,X0,X1,sK5)
      | ~ m1_subset_1(k11_mcart_1(sK0,sK1,X0,X1,sK5),sK3)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k10_mcart_1(sK0,sK1,X0,X1,sK5),sK2)
      | sK4 = k11_mcart_1(sK0,sK1,X0,X1,sK5)
      | ~ m1_subset_1(k11_mcart_1(sK0,sK1,X0,X1,sK5),sK3)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK0
      | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,X0,X1)) ) ),
    inference(resolution,[],[f33,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k8_mcart_1(X0,sK1,X1,X2,sK5),sK0)
      | ~ m1_subset_1(k10_mcart_1(X0,sK1,X1,X2,sK5),sK2)
      | sK4 = k11_mcart_1(X0,sK1,X1,X2,sK5)
      | ~ m1_subset_1(k11_mcart_1(X0,sK1,X1,X2,sK5),sK3)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(X0,sK1,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f32,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_mcart_1(X0,sK1,X1,X2,sK5),sK3)
      | ~ m1_subset_1(k10_mcart_1(X0,sK1,X1,X2,sK5),sK2)
      | sK4 = k11_mcart_1(X0,sK1,X1,X2,sK5)
      | ~ m1_subset_1(k8_mcart_1(X0,sK1,X1,X2,sK5),sK0)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(X0,sK1,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_mcart_1(X0,sK1,X1,X2,sK5),sK3)
      | ~ m1_subset_1(k10_mcart_1(X0,sK1,X1,X2,sK5),sK2)
      | sK4 = k11_mcart_1(X0,sK1,X1,X2,sK5)
      | ~ m1_subset_1(k8_mcart_1(X0,sK1,X1,X2,sK5),sK0)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(X0,sK1,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK5,k4_zfmisc_1(X0,sK1,X1,X2)) ) ),
    inference(resolution,[],[f30,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,sK5),sK1)
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,sK5),sK3)
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,sK5),sK2)
      | sK4 = k11_mcart_1(X0,X1,X2,X3,sK5)
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,sK5),sK0)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK5 != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = sK4
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),sK3)
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),sK2)
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),sK1)
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),sK0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f18,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f18,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X9
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
