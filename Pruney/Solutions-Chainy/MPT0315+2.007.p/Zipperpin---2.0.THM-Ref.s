%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RbLwDmWKCL

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  428 ( 690 expanded)
%              Number of equality atoms :   31 (  46 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
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
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
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
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X15 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','18','21'])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','33','34'])).

thf('36',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('39',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['22','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RbLwDmWKCL
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:59:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 210 iterations in 0.064s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(t127_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.53       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.53          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.21/0.53          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (((r1_xboole_0 @ sk_C @ sk_D)) <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.53      inference('split', [status(esa)], ['1'])).
% 0.21/0.53  thf(t83_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((((k4_xboole_0 @ sk_C @ sk_D) = (sk_C)))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf(t48_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.21/0.53           = (k3_xboole_0 @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((((k4_xboole_0 @ sk_C @ sk_C) = (k3_xboole_0 @ sk_C @ sk_D)))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf(t3_boole, axiom,
% 0.21/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.53  thf('7', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.21/0.53           = (k3_xboole_0 @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf(t2_boole, axiom,
% 0.21/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.53  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((((k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_D)))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.53  thf(t123_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.21/0.53       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         ((k2_zfmisc_1 @ (k3_xboole_0 @ X15 @ X17) @ (k3_xboole_0 @ X16 @ X18))
% 0.21/0.53           = (k3_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 0.21/0.53              (k2_zfmisc_1 @ X17 @ X18)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.53  thf(t75_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.53          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X7 @ X8)
% 0.21/0.53          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ 
% 0.21/0.53             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.53             (k2_zfmisc_1 @ X2 @ X0))
% 0.21/0.53          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i]:
% 0.21/0.53          (~ (r1_xboole_0 @ 
% 0.21/0.53              (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 0.21/0.53              (k2_zfmisc_1 @ X0 @ sk_D))
% 0.21/0.53           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ 
% 0.21/0.53              (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.53  thf(t113_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.21/0.53          | ((X14) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('19', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.53  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i]:
% 0.21/0.53          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D)))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_C @ sk_D)))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '18', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['1'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.21/0.53           = (k3_xboole_0 @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ 
% 0.21/0.53             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.53             (k2_zfmisc_1 @ X2 @ X0))
% 0.21/0.53          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i]:
% 0.21/0.53          (~ (r1_xboole_0 @ 
% 0.21/0.53              (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.53              (k2_zfmisc_1 @ sk_B @ X0))
% 0.21/0.53           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.21/0.53              (k2_zfmisc_1 @ sk_B @ X0))))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.21/0.53          | ((X13) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X14 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.53  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((![X0 : $i, X1 : $i]:
% 0.21/0.53          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.21/0.53         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ 
% 0.21/0.53          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('37', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((r1_xboole_0 @ sk_C @ sk_D)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.53      inference('split', [status(esa)], ['1'])).
% 0.21/0.53  thf('39', plain, (((r1_xboole_0 @ sk_C @ sk_D))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['22', '39'])).
% 0.21/0.53  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
