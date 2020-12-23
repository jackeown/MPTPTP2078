%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wCu8o6FsHl

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 179 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  460 (1332 expanded)
%              Number of equality atoms :   52 ( 156 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k3_subset_1 @ X7 @ X8 ) )
      | ( X8
        = ( k1_subset_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X8 @ ( k3_subset_1 @ X7 @ X8 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k3_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( ( k3_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8
       != ( k1_subset_1 @ X7 ) )
      | ( r1_tarski @ X8 @ ( k3_subset_1 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('17',plain,(
    ! [X7: $i] :
      ( ~ ( m1_subset_1 @ ( k1_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ ( k1_subset_1 @ X7 ) @ ( k3_subset_1 @ X7 @ ( k1_subset_1 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('23',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('25',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(demod,[status(thm)],['17','18','19','20','21','25'])).

thf('27',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('33',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('34',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('42',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['15','40','41'])).

thf('43',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['13','42'])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','43'])).

thf('45',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('46',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['2','44','45'])).

thf('47',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('48',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('49',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['15','40'])).

thf('51',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wCu8o6FsHl
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 60 iterations in 0.021s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(t39_subset_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.22/0.49         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.22/0.49            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.22/0.49  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.22/0.49          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.49      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t38_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.49         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X8 @ (k3_subset_1 @ X7 @ X8))
% 0.22/0.49          | ((X8) = (k1_subset_1 @ X7))
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.22/0.49  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('5', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X8 @ (k3_subset_1 @ X7 @ X8))
% 0.22/0.49          | ((X8) = (k1_xboole_0))
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.22/0.49        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.49        | ((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.49  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k3_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k3_subset_1 @ X2 @ X3) @ (k1_zfmisc_1 @ X2))
% 0.22/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.22/0.49        | ((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['7', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.22/0.49        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.22/0.49         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.22/0.49        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.22/0.49       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.49      inference('split', [status(esa)], ['14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (((X8) != (k1_subset_1 @ X7))
% 0.22/0.49          | (r1_tarski @ X8 @ (k3_subset_1 @ X7 @ X8))
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X7 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ (k1_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))
% 0.22/0.49          | (r1_tarski @ (k1_subset_1 @ X7) @ 
% 0.22/0.49             (k3_subset_1 @ X7 @ (k1_subset_1 @ X7))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.49  thf('18', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.49  thf(t4_subset_1, axiom,
% 0.22/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.49  thf('20', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.49  thf('21', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.49  thf(t22_subset_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X6 : $i]:
% 0.22/0.49         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.22/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.49  thf('23', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('24', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.49  thf('25', plain, (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.22/0.49  thf('26', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '18', '19', '20', '21', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.22/0.49          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.49      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain, (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.22/0.49  thf('31', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf('32', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['12'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.22/0.49         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['14'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.49         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.22/0.49             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.22/0.49         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.22/0.49             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.22/0.49         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.22/0.49             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.22/0.49       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '39'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.22/0.49       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['12'])).
% 0.22/0.49  thf('42', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['15', '40', '41'])).
% 0.22/0.49  thf('43', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['13', '42'])).
% 0.22/0.49  thf('44', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['11', '43'])).
% 0.22/0.49  thf('45', plain, (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.22/0.49  thf('46', plain, (((sk_A) = (sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '44', '45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.22/0.49         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['14'])).
% 0.22/0.49  thf('48', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.49      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.49  thf('50', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['15', '40'])).
% 0.22/0.49  thf('51', plain, (((sk_B) != (sk_A))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['49', '50'])).
% 0.22/0.49  thf('52', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['46', '51'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
