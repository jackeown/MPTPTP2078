%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AvVaFx8vyb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:16 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 109 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  470 ( 900 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_D )
      = sk_C )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_C )
      = ( k3_xboole_0 @ sk_C @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X12 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) @ X8 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) ) @ X8 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['22','24','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('33',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','37','38'])).

thf('40',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('43',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['26','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AvVaFx8vyb
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 407 iterations in 0.156s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.60  thf(t127_zfmisc_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.39/0.60       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.39/0.60          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.39/0.60          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_C @ sk_D)) <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.39/0.60      inference('split', [status(esa)], ['1'])).
% 0.39/0.60  thf(t83_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (![X4 : $i, X5 : $i]:
% 0.39/0.60         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_C @ sk_D) = (sk_C)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.60  thf(t48_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.39/0.60           = (k3_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_C @ sk_C) = (k3_xboole_0 @ sk_C @ sk_D)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.60  thf(t3_boole, axiom,
% 0.39/0.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.60  thf('7', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.39/0.60           = (k3_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.60  thf(t2_boole, axiom,
% 0.39/0.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.60  thf('10', plain,
% 0.39/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.60  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      ((((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.39/0.60      inference('demod', [status(thm)], ['6', '11'])).
% 0.39/0.60  thf(t123_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.60     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.39/0.60       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.60         ((k2_zfmisc_1 @ (k3_xboole_0 @ X12 @ X14) @ (k3_xboole_0 @ X13 @ X15))
% 0.39/0.60           = (k3_xboole_0 @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 0.39/0.60              (k2_zfmisc_1 @ X14 @ X15)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.39/0.60           = (k3_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.39/0.60           = (k3_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ 
% 0.39/0.60           (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.39/0.60           = (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ 
% 0.39/0.60              (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.39/0.60      inference('sup+', [status(thm)], ['13', '16'])).
% 0.39/0.60  thf(t90_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 0.39/0.60  thf('18', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i]:
% 0.39/0.60         (r1_xboole_0 @ (k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) @ X8)),
% 0.39/0.60      inference('cnf', [status(esa)], [t90_xboole_1])).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i]:
% 0.39/0.60         (r1_xboole_0 @ (k3_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8)) @ X8)),
% 0.39/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.60         (r1_xboole_0 @ 
% 0.39/0.60          (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ 
% 0.39/0.60           (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.39/0.60          (k2_zfmisc_1 @ X2 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['17', '20'])).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      ((![X0 : $i, X1 : $i]:
% 0.39/0.60          (r1_xboole_0 @ 
% 0.39/0.60           (k4_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ 
% 0.39/0.60            (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)) @ 
% 0.39/0.60           (k2_zfmisc_1 @ X0 @ sk_D)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['12', '21'])).
% 0.39/0.60  thf(t113_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.60  thf('23', plain,
% 0.39/0.60      (![X10 : $i, X11 : $i]:
% 0.39/0.60         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.39/0.60          | ((X11) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('24', plain,
% 0.39/0.60      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['23'])).
% 0.39/0.60  thf('25', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.60  thf('26', plain,
% 0.39/0.60      ((![X0 : $i, X1 : $i]:
% 0.39/0.60          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.39/0.60      inference('demod', [status(thm)], ['22', '24', '25'])).
% 0.39/0.60  thf('27', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('split', [status(esa)], ['1'])).
% 0.39/0.60  thf('28', plain,
% 0.39/0.60      (![X4 : $i, X5 : $i]:
% 0.39/0.60         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.39/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.60  thf('29', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.60  thf('30', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.39/0.60           = (k3_xboole_0 @ X2 @ X3))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('31', plain,
% 0.39/0.60      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['29', '30'])).
% 0.39/0.60  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.60  thf('33', plain,
% 0.39/0.60      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.60         (r1_xboole_0 @ 
% 0.39/0.60          (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ 
% 0.39/0.60           (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.39/0.60          (k2_zfmisc_1 @ X2 @ X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['17', '20'])).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      ((![X0 : $i, X1 : $i]:
% 0.39/0.60          (r1_xboole_0 @ 
% 0.39/0.60           (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.39/0.60            (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.39/0.60           (k2_zfmisc_1 @ sk_B @ X0)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      (![X10 : $i, X11 : $i]:
% 0.39/0.60         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.39/0.60          | ((X10) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.39/0.60  thf('38', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.60  thf('39', plain,
% 0.39/0.60      ((![X0 : $i, X1 : $i]:
% 0.39/0.60          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.39/0.60         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('demod', [status(thm)], ['35', '37', '38'])).
% 0.39/0.60  thf('40', plain,
% 0.39/0.60      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.39/0.60          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('41', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      (((r1_xboole_0 @ sk_C @ sk_D)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.60      inference('split', [status(esa)], ['1'])).
% 0.39/0.60  thf('43', plain, (((r1_xboole_0 @ sk_C @ sk_D))),
% 0.39/0.60      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.39/0.60      inference('simpl_trail', [status(thm)], ['26', '43'])).
% 0.39/0.60  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
