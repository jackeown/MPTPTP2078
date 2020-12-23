%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tHy9OoGUUT

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 483 expanded)
%              Number of leaves         :   22 ( 159 expanded)
%              Depth                    :   16
%              Number of atoms          :  947 (14416 expanded)
%              Number of equality atoms :   96 (1800 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t61_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ~ ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
               => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                  & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                  & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                    = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                  & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                    = ( k2_mcart_1 @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X15
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k9_mcart_1 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k10_mcart_1 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k11_mcart_1 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_E
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('10',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_mcart_1 @ sk_E )
    = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( sk_E
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_mcart_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k4_tarski @ ( k3_mcart_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('20',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k1_mcart_1 @ sk_E )
    = ( k3_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('33',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( k2_mcart_1 @ sk_E )
    = ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('37',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['34'])).

thf('38',plain,
    ( ( ( k2_mcart_1 @ sk_E )
     != ( k2_mcart_1 @ sk_E ) )
   <= ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
    = ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('41',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('42',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
   <= ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    = ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('45',plain,
    ( ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('46',plain,
    ( ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
   <= ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
     != ( k2_mcart_1 @ sk_E ) ) ),
    inference(split,[status(esa)],['34'])).

thf('49',plain,(
    ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference('sat_resolution*',[status(thm)],['39','43','47','48'])).

thf('50',plain,(
    ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(simpl_trail,[status(thm)],['35','49'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tHy9OoGUUT
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:25:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 55 iterations in 0.029s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(t61_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ~( ![E:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.47                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.47                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.20/0.47                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47             ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47             ( ~( ![E:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47                    ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                        ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.47                      ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                        ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.47                      ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                        ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.20/0.47                      ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                        ( k2_mcart_1 @ E ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t61_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t60_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ~( ![E:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47                 ( ( E ) =
% 0.20/0.47                   ( k4_mcart_1 @
% 0.20/0.47                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.47                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.47                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.47                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.47         (((X11) = (k1_xboole_0))
% 0.20/0.47          | ((X12) = (k1_xboole_0))
% 0.20/0.47          | ((X13) = (k1_xboole_0))
% 0.20/0.47          | ((X15)
% 0.20/0.47              = (k4_mcart_1 @ (k8_mcart_1 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 0.20/0.47                 (k9_mcart_1 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 0.20/0.47                 (k10_mcart_1 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 0.20/0.47                 (k11_mcart_1 @ X11 @ X12 @ X13 @ X14 @ X15)))
% 0.20/0.47          | ~ (m1_subset_1 @ X15 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X14))
% 0.20/0.47          | ((X14) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t60_mcart_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((((sk_D) = (k1_xboole_0))
% 0.20/0.47        | ((sk_E)
% 0.20/0.47            = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47               (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47               (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47               (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))
% 0.20/0.47        | ((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((sk_E)
% 0.20/0.47         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((sk_E)
% 0.20/0.47         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.47  thf(d4_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.47       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.47           = (k4_tarski @ (k3_mcart_1 @ X3 @ X4 @ X5) @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.47  thf(t7_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.47       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((k2_mcart_1 @ sk_E) = (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.47      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (((sk_E)
% 0.20/0.47         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k2_mcart_1 @ sk_E)))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((k4_mcart_1 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.47           = (k4_tarski @ (k3_mcart_1 @ X3 @ X4 @ X5) @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.47           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (((k1_mcart_1 @ sk_E)
% 0.20/0.47         = (k3_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['13', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((k1_mcart_1 @ sk_E)
% 0.20/0.47         = (k3_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['13', '16'])).
% 0.20/0.47  thf(d3_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.47           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.20/0.47         = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.47      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (((k1_mcart_1 @ sk_E)
% 0.20/0.47         = (k3_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.20/0.47           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.20/0.47         = (k4_tarski @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['23', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.20/0.47         = (k4_tarski @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['23', '26'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.20/0.47         = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.47      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((k1_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.20/0.47         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))) @ 
% 0.20/0.47            (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.20/0.47         = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.47      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          != (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.20/0.47        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47            != (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.20/0.47        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47            != (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.20/0.47        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47            != (k2_mcart_1 @ sk_E)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          != (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47                = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))))),
% 0.20/0.47      inference('split', [status(esa)], ['34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (((k2_mcart_1 @ sk_E) = (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.47      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          != (k2_mcart_1 @ sk_E)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47                = (k2_mcart_1 @ sk_E))))),
% 0.20/0.47      inference('split', [status(esa)], ['34'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((((k2_mcart_1 @ sk_E) != (k2_mcart_1 @ sk_E)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47                = (k2_mcart_1 @ sk_E))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (((k2_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.20/0.47         = (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.47      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          != (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47                = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.20/0.47      inference('split', [status(esa)], ['34'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E))
% 0.20/0.47          != (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47                = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.20/0.47         = (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.20/0.47      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          != (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47                = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))))),
% 0.20/0.47      inference('split', [status(esa)], ['34'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      ((((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.20/0.47          != (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47                = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      ((((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))) | 
% 0.20/0.47       ~
% 0.20/0.47       (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))) | 
% 0.20/0.47       ~
% 0.20/0.47       (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))) | 
% 0.20/0.47       ~
% 0.20/0.47       (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) = (k2_mcart_1 @ sk_E)))),
% 0.20/0.47      inference('split', [status(esa)], ['34'])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47          = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['39', '43', '47', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.20/0.47         != (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['35', '49'])).
% 0.20/0.47  thf('51', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['33', '50'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
