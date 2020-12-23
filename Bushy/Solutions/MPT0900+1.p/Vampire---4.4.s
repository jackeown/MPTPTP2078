%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t60_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 612 expanded)
%              Number of leaves         :   20 ( 255 expanded)
%              Depth                    :   16
%              Number of atoms          :  544 (3724 expanded)
%              Number of equality atoms :  398 (2758 expanded)
%              Maximal formula depth    :   19 (  11 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1487,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1484,f67])).

fof(f67,plain,(
    k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) != sK4
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f37,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,X4),k9_mcart_1(sK0,sK1,sK2,sK3,X4),k10_mcart_1(sK0,sK1,sK2,sK3,X4),k11_mcart_1(sK0,sK1,sK2,sK3,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
     => ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,sK4),k9_mcart_1(X0,X1,X2,X3,sK4),k10_mcart_1(X0,X1,X2,X3,sK4),k11_mcart_1(X0,X1,X2,X3,sK4)) != sK4
        & m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) != X4
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',t60_mcart_1)).

fof(f1484,plain,(
    k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) = sK4 ),
    inference(backward_demodulation,[],[f1474,f1463])).

fof(f1463,plain,(
    k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) = sK4 ),
    inference(backward_demodulation,[],[f1453,f1442])).

fof(f1442,plain,(
    k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) = sK4 ),
    inference(backward_demodulation,[],[f1432,f1421])).

fof(f1421,plain,(
    k4_mcart_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) = sK4 ),
    inference(backward_demodulation,[],[f1411,f1134])).

fof(f1134,plain,(
    k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4)) = sK4 ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f65,f66,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f27,f42,f41,f40,f39])).

fof(f39,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(X5,sK6(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(X5,X6,X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(X5,X6,sK7(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X6,X7,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(X5,X6,X7,X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(X5,X6,X7,sK8(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK8(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',l68_mcart_1)).

fof(f66,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f38])).

fof(f1411,plain,(
    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f65,f66,f1399])).

fof(f1399,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,sK4) = sK5(sK0,sK1,sK2,sK3,sK4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f1395,f1134])).

fof(f1395,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))) = sK5(sK0,sK1,sK2,sK3,sK4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f1394,f1134])).

fof(f1394,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f97,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',dt_k8_mcart_1)).

fof(f97,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X10
      | ~ m1_subset_1(k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X10
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK21(X4,X5) != X5
                    & k4_mcart_1(sK21(X4,X5),sK22(X4,X5),sK23(X4,X5),sK24(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21,sK22,sK23,sK24])],[f57,f58])).

fof(f58,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X6
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK21(X4,X5) != X5
        & k4_mcart_1(sK21(X4,X5),sK22(X4,X5),sK23(X4,X5),sK24(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X10
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X6
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k8_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X6
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ( k8_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X6 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',d8_mcart_1)).

fof(f1432,plain,(
    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6(sK0,sK1,sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f65,f66,f1400])).

fof(f1400,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X4,X5,X6,X7))
      | k9_mcart_1(X4,X5,X6,X7,sK4) = sK6(sK0,sK1,sK2,sK3,sK4)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f1396,f1134])).

fof(f1396,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X4,X5,X6,X7))
      | k9_mcart_1(X4,X5,X6,X7,k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))) = sK6(sK0,sK1,sK2,sK3,sK4)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | k1_xboole_0 = X5
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f1393,f1134])).

fof(f1393,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f95,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',dt_k9_mcart_1)).

fof(f95,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK18(X4,X5) != X5
                    & k4_mcart_1(sK17(X4,X5),sK18(X4,X5),sK19(X4,X5),sK20(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18,sK19,sK20])],[f53,f54])).

fof(f54,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X7
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK18(X4,X5) != X5
        & k4_mcart_1(sK17(X4,X5),sK18(X4,X5),sK19(X4,X5),sK20(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X7 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',d9_mcart_1)).

fof(f1453,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7(sK0,sK1,sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f65,f66,f1401])).

fof(f1401,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11))
      | k10_mcart_1(X8,X9,X10,X11,sK4) = sK7(sK0,sK1,sK2,sK3,sK4)
      | k1_xboole_0 = X11
      | k1_xboole_0 = X10
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8 ) ),
    inference(forward_demodulation,[],[f1397,f1134])).

fof(f1397,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11))
      | k10_mcart_1(X8,X9,X10,X11,k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))) = sK7(sK0,sK1,sK2,sK3,sK4)
      | k1_xboole_0 = X11
      | k1_xboole_0 = X10
      | k1_xboole_0 = X9
      | k1_xboole_0 = X8 ) ),
    inference(superposition,[],[f1392,f1134])).

fof(f1392,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f93,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',dt_k10_mcart_1)).

fof(f93,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X12
      | ~ m1_subset_1(k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X12
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK15(X4,X5) != X5
                    & k4_mcart_1(sK13(X4,X5),sK14(X4,X5),sK15(X4,X5),sK16(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f49,f50])).

fof(f50,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X8
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK15(X4,X5) != X5
        & k4_mcart_1(sK13(X4,X5),sK14(X4,X5),sK15(X4,X5),sK16(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X2)
                 => ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X8 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',d10_mcart_1)).

fof(f1474,plain,(
    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8(sK0,sK1,sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f62,f63,f64,f65,f66,f1402])).

fof(f1402,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X12,X13,X14,X15))
      | k11_mcart_1(X12,X13,X14,X15,sK4) = sK8(sK0,sK1,sK2,sK3,sK4)
      | k1_xboole_0 = X15
      | k1_xboole_0 = X14
      | k1_xboole_0 = X13
      | k1_xboole_0 = X12 ) ),
    inference(forward_demodulation,[],[f1398,f1134])).

fof(f1398,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X12,X13,X14,X15))
      | k11_mcart_1(X12,X13,X14,X15,k4_mcart_1(sK5(sK0,sK1,sK2,sK3,sK4),sK6(sK0,sK1,sK2,sK3,sK4),sK7(sK0,sK1,sK2,sK3,sK4),sK8(sK0,sK1,sK2,sK3,sK4))) = sK8(sK0,sK1,sK2,sK3,sK4)
      | k1_xboole_0 = X15
      | k1_xboole_0 = X14
      | k1_xboole_0 = X13
      | k1_xboole_0 = X12 ) ),
    inference(superposition,[],[f1391,f1134])).

fof(f1391,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f91,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',dt_k11_mcart_1)).

fof(f91,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X13
      | ~ m1_subset_1(k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X13
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK12(X4,X5) != X5
                    & k4_mcart_1(sK9(X4,X5),sK10(X4,X5),sK11(X4,X5),sK12(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X13
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12])],[f45,f46])).

fof(f46,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X9
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK12(X4,X5) != X5
        & k4_mcart_1(sK9(X4,X5),sK10(X4,X5),sK11(X4,X5),sK12(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X9
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X13
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X9
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X9
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k11_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X3) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X9
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X3) )
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
             => ! [X5] :
                  ( m1_subset_1(X5,X3)
                 => ( k11_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X9 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t60_mcart_1.p',d11_mcart_1)).
%------------------------------------------------------------------------------
