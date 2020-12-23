%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 302 expanded)
%              Number of leaves         :    5 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  215 (2157 expanded)
%              Number of equality atoms :  148 (1306 expanded)
%              Maximal formula depth    :   23 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f17,f16,f15,f14,f18,f31,f60])).

fof(f60,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10),X11))
      | sK4 = k10_mcart_1(X8,X9,X10,X11,sK5)
      | k1_xboole_0 = X8
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11 ) ),
    inference(forward_demodulation,[],[f55,f51])).

fof(f51,plain,(
    sK4 = sK8(sK0,sK1,sK2,sK3,sK5) ),
    inference(unit_resulting_resolution,[],[f49,f45,f47,f48,f46,f12])).

fof(f12,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X8 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f46,plain,(
    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5)) ),
    inference(unit_resulting_resolution,[],[f15,f14,f17,f16,f31,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f48,plain,(
    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1) ),
    inference(unit_resulting_resolution,[],[f14,f15,f17,f16,f31,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2) ),
    inference(unit_resulting_resolution,[],[f14,f15,f17,f16,f31,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3) ),
    inference(unit_resulting_resolution,[],[f14,f15,f17,f16,f31,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(unit_resulting_resolution,[],[f14,f15,f17,f16,f31,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10),X11))
      | k1_xboole_0 = X8
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | sK8(sK0,sK1,sK2,sK3,sK5) = k10_mcart_1(X8,X9,X10,X11,sK5) ) ),
    inference(superposition,[],[f42,f46])).

fof(f42,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(definition_unfolding,[],[f21,f30])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f31,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f13,f30])).

fof(f13,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (9347)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (9352)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (9356)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (9360)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (9352)Refutation not found, incomplete strategy% (9352)------------------------------
% 0.19/0.52  % (9352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (9368)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (9372)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (9360)Refutation not found, incomplete strategy% (9360)------------------------------
% 0.19/0.52  % (9360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (9347)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % (9365)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f17,f16,f15,f14,f18,f31,f60])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10),X11)) | sK4 = k10_mcart_1(X8,X9,X10,X11,sK5) | k1_xboole_0 = X8 | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11) )),
% 0.19/0.52    inference(forward_demodulation,[],[f55,f51])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    sK4 = sK8(sK0,sK1,sK2,sK3,sK5)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f49,f45,f47,f48,f46,f12])).
% 0.19/0.52  fof(f12,plain,(
% 0.19/0.52    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X8) )),
% 0.19/0.52    inference(cnf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,plain,(
% 0.19/0.52    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.19/0.52    inference(flattening,[],[f7])).
% 0.19/0.52  fof(f7,plain,(
% 0.19/0.52    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.52    inference(negated_conjecture,[],[f5])).
% 0.19/0.52  fof(f5,conjecture,(
% 0.19/0.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    sK5 = k4_mcart_1(sK6(sK0,sK1,sK2,sK3,sK5),sK7(sK0,sK1,sK2,sK3,sK5),sK8(sK0,sK1,sK2,sK3,sK5),sK9(sK0,sK1,sK2,sK3,sK5))),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f15,f14,f17,f16,f31,f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.19/0.52    inference(definition_unfolding,[],[f24,f30])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.19/0.53    inference(definition_unfolding,[],[f28,f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.19/0.53    inference(ennf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK5),sK1)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f14,f15,f17,f16,f31,f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(definition_unfolding,[],[f26,f30])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK5),sK2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f14,f15,f17,f16,f31,f38])).
% 0.19/0.53  fof(f38,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(definition_unfolding,[],[f25,f30])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    m1_subset_1(sK9(sK0,sK1,sK2,sK3,sK5),sK3)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f14,f15,f17,f16,f31,f40])).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(definition_unfolding,[],[f23,f30])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    m1_subset_1(sK6(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f14,f15,f17,f16,f31,f36])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(definition_unfolding,[],[f27,f30])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10),X11)) | k1_xboole_0 = X8 | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11 | sK8(sK0,sK1,sK2,sK3,sK5) = k10_mcart_1(X8,X9,X10,X11,sK5)) )),
% 0.19/0.53    inference(superposition,[],[f42,f46])).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7) )),
% 0.19/0.53    inference(equality_resolution,[],[f33])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.19/0.53    inference(definition_unfolding,[],[f21,f30])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f10,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.19/0.53    inference(flattening,[],[f9])).
% 0.19/0.53  fof(f9,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.19/0.53    inference(ennf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.19/0.53    inference(definition_unfolding,[],[f13,f30])).
% 0.19/0.53  fof(f13,plain,(
% 0.19/0.53    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f14,plain,(
% 0.19/0.53    k1_xboole_0 != sK0),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    k1_xboole_0 != sK1),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    k1_xboole_0 != sK2),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    k1_xboole_0 != sK3),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (9347)------------------------------
% 0.19/0.53  % (9347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (9347)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (9347)Memory used [KB]: 6396
% 0.19/0.53  % (9347)Time elapsed: 0.119 s
% 0.19/0.53  % (9347)------------------------------
% 0.19/0.53  % (9347)------------------------------
% 0.19/0.53  % (9345)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (9342)Success in time 0.174 s
%------------------------------------------------------------------------------
