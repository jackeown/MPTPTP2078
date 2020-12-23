%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XQ2x3HYCJA

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  84 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   19
%              Number of atoms          :  404 ( 819 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t139_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
         => ( r1_tarski @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i,C: $i,D: $i] :
            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
              | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
           => ( r1_tarski @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('5',plain,
    ( ( ( r1_tarski @ sk_B @ sk_D )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
        | ( r1_tarski @ sk_B @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['1'])).

thf('24',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ sk_D @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['2','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('27',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['19'])).

thf('35',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XQ2x3HYCJA
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 35 iterations in 0.032s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(t139_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52       ( ![B:$i,C:$i,D:$i]:
% 0.22/0.52         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.22/0.52             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.22/0.52           ( r1_tarski @ B @ D ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52          ( ![B:$i,C:$i,D:$i]:
% 0.22/0.52            ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.22/0.52                ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.22/0.52              ( r1_tarski @ B @ D ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t139_zfmisc_1])).
% 0.22/0.52  thf('0', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.22/0.52        | (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.22/0.52           (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))
% 0.22/0.52         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_D @ sk_C))))),
% 0.22/0.52      inference('split', [status(esa)], ['1'])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))
% 0.22/0.52         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.22/0.52      inference('split', [status(esa)], ['1'])).
% 0.22/0.52  thf(t138_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.22/0.52       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.52         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.22/0.52          | ~ (r1_tarski @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 0.22/0.52               (k2_zfmisc_1 @ X15 @ X16))
% 0.22/0.52          | (r1_tarski @ X14 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((((r1_tarski @ sk_B @ sk_D)
% 0.22/0.52         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.22/0.52         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.52         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.22/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf(t117_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.22/0.52            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.22/0.52          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         (((X10) = (k1_xboole_0))
% 0.22/0.52          | (r1_tarski @ X11 @ X12)
% 0.22/0.52          | ~ (r1_tarski @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 0.22/0.52               (k2_zfmisc_1 @ X10 @ X12)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (~ (r1_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X0))
% 0.22/0.52           | (r1_tarski @ sk_B @ X0)
% 0.22/0.52           | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.52  thf('10', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      ((![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.22/0.52         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.22/0.52               (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.52  thf('17', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.52  thf(t68_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.52       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ X7 @ X8)
% 0.22/0.52          | (v1_xboole_0 @ X9)
% 0.22/0.52          | ~ (r1_tarski @ X9 @ X7)
% 0.22/0.52          | ~ (r1_tarski @ X9 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.22/0.52          | ~ (r1_tarski @ X1 @ X0)
% 0.22/0.52          | (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['19'])).
% 0.22/0.52  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['15', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))) | 
% 0.22/0.52       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['1'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      ((r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_A) @ (k2_zfmisc_1 @ sk_D @ sk_C))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['2', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 0.22/0.52          | ~ (r1_tarski @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 0.22/0.52               (k2_zfmisc_1 @ X15 @ X16))
% 0.22/0.52          | (r1_tarski @ X13 @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ sk_D)
% 0.22/0.52        | ((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('29', plain, (((k2_zfmisc_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         (((X10) = (k1_xboole_0))
% 0.22/0.52          | (r1_tarski @ X11 @ X12)
% 0.22/0.52          | ~ (r1_tarski @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 0.22/0.52               (k2_zfmisc_1 @ X10 @ X12)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ X0))
% 0.22/0.52          | (r1_tarski @ sk_A @ X0)
% 0.22/0.52          | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['19'])).
% 0.22/0.52  thf('35', plain, ((((sk_B) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('39', plain, ($false),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '37', '38'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
