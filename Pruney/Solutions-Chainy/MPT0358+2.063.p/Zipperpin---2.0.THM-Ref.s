%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tbFYwAI7aO

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 160 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  403 (1330 expanded)
%              Number of equality atoms :   39 ( 124 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['8','13'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( k1_subset_1 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('24',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','30','31'])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['20','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['8','13'])).

thf('37',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['18','35','36'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k1_subset_1 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('42',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['22','30'])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tbFYwAI7aO
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:59:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 47 iterations in 0.036s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(t38_subset_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.52         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.52            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.22/0.52  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k3_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.22/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d5_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.22/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.22/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.52         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.22/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['8', '13'])).
% 0.22/0.52  thf(t79_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X7)),
% 0.22/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.52  thf(t69_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.52       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ X4 @ X5)
% 0.22/0.52          | ~ (r1_tarski @ X4 @ X5)
% 0.22/0.52          | (v1_xboole_0 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.52          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.52        | (v1_xboole_0 @ (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.22/0.52        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.22/0.52        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.22/0.52       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['21'])).
% 0.22/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('23', plain, (![X8 : $i]: ((k1_subset_1 @ X8) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('split', [status(esa)], ['21'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.22/0.52             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.52  thf('29', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.52       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.52       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('32', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['22', '30', '31'])).
% 0.22/0.52  thf('33', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['20', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('35', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['8', '13'])).
% 0.22/0.52  thf('37', plain, ((v1_xboole_0 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '35', '36'])).
% 0.22/0.52  thf(l13_xboole_0, axiom,
% 0.22/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.52  thf('39', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.22/0.52         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['21'])).
% 0.22/0.52  thf('41', plain, (![X8 : $i]: ((k1_subset_1 @ X8) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['22', '30'])).
% 0.22/0.52  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['39', '44'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
