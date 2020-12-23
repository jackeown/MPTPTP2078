%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hFm90phrHU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:10 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  544 (1294 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t47_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( r1_xboole_0 @ D @ C ) )
               => ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( ( r1_tarski @ B @ C )
                    & ( r1_xboole_0 @ D @ C ) )
                 => ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_xboole_0 @ X13 @ X11 )
      | ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_D ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_D )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r1_xboole_0 @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ( r1_xboole_0 @ X16 @ ( k3_subset_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t44_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('16',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_xboole_0 @ X13 @ X11 )
      | ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_xboole_0 @ X13 @ X11 )
      | ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_xboole_0 @ sk_D @ sk_C )
    | ( r1_tarski @ sk_D @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ sk_D @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ( r1_tarski @ ( k3_subset_1 @ X9 @ X8 ) @ ( k3_subset_1 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ( r1_xboole_0 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ sk_D )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('41',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ sk_D ),
    inference(demod,[status(thm)],['38','41'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ sk_D )
    = ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
      | ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['21','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['6','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hFm90phrHU
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 231 iterations in 0.134s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(t47_subset_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58           ( ![D:$i]:
% 0.40/0.58             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58               ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.40/0.58                 ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58          ( ![C:$i]:
% 0.40/0.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58              ( ![D:$i]:
% 0.40/0.58                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58                  ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.40/0.58                    ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t47_subset_1])).
% 0.40/0.58  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t43_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.40/0.58             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.58          | ~ (r1_xboole_0 @ X13 @ X11)
% 0.40/0.58          | (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X11))
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.58          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_D))
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ sk_D))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      ((~ (r1_xboole_0 @ sk_B @ sk_D)
% 0.40/0.58        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['0', '3'])).
% 0.40/0.58  thf('5', plain, (~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('6', plain, (~ (r1_xboole_0 @ sk_B @ sk_D)),
% 0.40/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.40/0.58  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('8', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t44_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.40/0.58             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.40/0.58          | ~ (r1_tarski @ X16 @ X14)
% 0.40/0.58          | (r1_xboole_0 @ X16 @ (k3_subset_1 @ X15 @ X14))
% 0.40/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t44_subset_1])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.58          | (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.40/0.58        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.40/0.58  thf('12', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('13', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.58  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(dt_k3_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.40/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.58          | ~ (r1_xboole_0 @ X13 @ X11)
% 0.40/0.58          | (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X11))
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.58          | (r1_tarski @ X0 @ 
% 0.40/0.58             (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.40/0.58        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '18'])).
% 0.40/0.58  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.40/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('22', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('23', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.58          | ~ (r1_xboole_0 @ X13 @ X11)
% 0.40/0.58          | (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X11))
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.58          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.40/0.58          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      ((~ (r1_xboole_0 @ sk_D @ sk_C)
% 0.40/0.58        | (r1_tarski @ sk_D @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['22', '25'])).
% 0.40/0.58  thf('27', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('28', plain, ((r1_tarski @ sk_D @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf(t31_subset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.58           ( ( r1_tarski @ B @ C ) <=>
% 0.40/0.58             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.40/0.58          | ~ (r1_tarski @ X10 @ X8)
% 0.40/0.58          | (r1_tarski @ (k3_subset_1 @ X9 @ X8) @ (k3_subset_1 @ X9 @ X10))
% 0.40/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.58          | (r1_tarski @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 0.40/0.58             (k3_subset_1 @ sk_A @ X0))
% 0.40/0.58          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 0.40/0.58         (k3_subset_1 @ sk_A @ sk_D))
% 0.40/0.58        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['28', '31'])).
% 0.40/0.58  thf('33', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 0.40/0.58        (k3_subset_1 @ sk_A @ sk_D))),
% 0.40/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf('35', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.40/0.58          | ~ (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X11))
% 0.40/0.58          | (r1_xboole_0 @ X13 @ X11)
% 0.40/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.58          | (r1_xboole_0 @ X0 @ sk_D)
% 0.40/0.58          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_D)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 0.40/0.58         sk_D)
% 0.40/0.58        | ~ (m1_subset_1 @ 
% 0.40/0.58             (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 0.40/0.58             (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['34', '37'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.40/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 0.40/0.58        (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ sk_D)),
% 0.40/0.58      inference('demod', [status(thm)], ['38', '41'])).
% 0.40/0.58  thf(t83_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.40/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 0.40/0.58         sk_D) = (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.40/0.58  thf(t106_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.40/0.58       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((r1_xboole_0 @ X0 @ X2)
% 0.40/0.58          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (r1_tarski @ X0 @ 
% 0.40/0.58             (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.40/0.58          | (r1_xboole_0 @ X0 @ sk_D))),
% 0.40/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.58  thf('47', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '46'])).
% 0.40/0.58  thf('48', plain, ($false), inference('demod', [status(thm)], ['6', '47'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
