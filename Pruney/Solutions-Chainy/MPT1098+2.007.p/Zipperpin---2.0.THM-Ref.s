%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d74jzoaNuZ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  336 ( 674 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(t33_finset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( v1_finset_1 @ A )
          & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ! [D: $i] :
              ~ ( ( v1_finset_1 @ D )
                & ( r1_tarski @ D @ B )
                & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_finset_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_finset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( v1_finset_1 @ E )
              & ( r1_tarski @ E @ C )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_finset_1 @ X10 )
      | ( r1_tarski @ ( sk_E @ X11 @ X12 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('2',plain,
    ( ( r1_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t119_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_finset_1 @ X10 )
      | ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( sk_D @ X11 @ X12 @ X10 ) @ ( sk_E @ X11 @ X12 @ X10 ) ) )
      | ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X13: $i] :
      ( ~ ( v1_finset_1 @ X13 )
      | ~ ( r1_tarski @ X13 @ sk_B )
      | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X13 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_finset_1 @ X10 )
      | ( v1_finset_1 @ ( sk_D @ X11 @ X12 @ X10 ) )
      | ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('22',plain,
    ( ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_finset_1 @ X10 )
      | ( r1_tarski @ ( sk_D @ X11 @ X12 @ X10 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('28',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['25','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d74jzoaNuZ
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 69 iterations in 0.050s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.51  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.51  thf(t33_finset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.51          ( ![D:$i]:
% 0.21/0.51            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.21/0.51                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ~( ( v1_finset_1 @ A ) & 
% 0.21/0.51             ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.51             ( ![D:$i]:
% 0.21/0.51               ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.21/0.51                    ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t33_finset_1])).
% 0.21/0.51  thf('0', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t32_finset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.51          ( ![D:$i,E:$i]:
% 0.21/0.51            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.21/0.51                 ( v1_finset_1 @ E ) & ( r1_tarski @ E @ C ) & 
% 0.21/0.51                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v1_finset_1 @ X10)
% 0.21/0.51          | (r1_tarski @ (sk_E @ X11 @ X12 @ X10) @ X11)
% 0.21/0.51          | ~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X12 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((r1_tarski @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.51        | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('4', plain, ((r1_tarski @ (sk_E @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.51  thf(t119_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.21/0.51       ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.51          | ~ (r1_tarski @ X8 @ X9)
% 0.21/0.51          | (r1_tarski @ (k2_zfmisc_1 @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.51          | ~ (r1_tarski @ X2 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.51          (k2_zfmisc_1 @ X0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.51  thf('10', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v1_finset_1 @ X10)
% 0.21/0.51          | (r1_tarski @ X10 @ 
% 0.21/0.51             (k2_zfmisc_1 @ (sk_D @ X11 @ X12 @ X10) @ (sk_E @ X11 @ X12 @ X10)))
% 0.21/0.51          | ~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X12 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((r1_tarski @ sk_A @ 
% 0.21/0.51         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51          (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.21/0.51        | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((r1_tarski @ sk_A @ 
% 0.21/0.51        (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51         (sk_E @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf(t1_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51       ( r1_tarski @ A @ C ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.51          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.51          | (r1_tarski @ X3 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_A @ X0)
% 0.21/0.51          | ~ (r1_tarski @ 
% 0.21/0.51               (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.51                (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.51               X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X13 : $i]:
% 0.21/0.51         (~ (v1_finset_1 @ X13)
% 0.21/0.51          | ~ (r1_tarski @ X13 @ sk_B)
% 0.21/0.51          | ~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X13 @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((~ (r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.51        | ~ (v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v1_finset_1 @ X10)
% 0.21/0.51          | (v1_finset_1 @ (sk_D @ X11 @ X12 @ X10))
% 0.21/0.51          | ~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X12 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)) | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain, ((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, (~ (r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '24'])).
% 0.21/0.51  thf('26', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v1_finset_1 @ X10)
% 0.21/0.51          | (r1_tarski @ (sk_D @ X11 @ X12 @ X10) @ X12)
% 0.21/0.51          | ~ (r1_tarski @ X10 @ (k2_zfmisc_1 @ X12 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.51        | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain, ((r1_tarski @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain, ($false), inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
