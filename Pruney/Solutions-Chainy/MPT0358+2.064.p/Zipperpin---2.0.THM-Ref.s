%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IJG58NUKpD

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 153 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  387 (1232 expanded)
%              Number of equality atoms :   46 ( 134 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k1_subset_1 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('16',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,
    ( ( ( k3_subset_1 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('31',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['14','32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['12','34'])).

thf('36',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','35'])).

thf('37',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('38',plain,(
    ! [X10: $i] :
      ( ( k1_subset_1 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('39',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['14','32'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IJG58NUKpD
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:54:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 102 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(t38_subset_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.49         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.49            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.21/0.49  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d5_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(t79_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X6)),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t83_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.21/0.49        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.21/0.49         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf(l32_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X2 : $i, X4 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.21/0.49         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.21/0.49        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.21/0.49       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['13'])).
% 0.21/0.49  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('15', plain, (![X10 : $i]: ((k1_subset_1 @ X10) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.49         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((((k3_subset_1 @ sk_A @ k1_xboole_0)
% 0.21/0.49          = (k4_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.21/0.49         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.49         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['21', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.21/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['13'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.21/0.49             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.21/0.49             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.21/0.49       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.21/0.49       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf('34', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['14', '32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['12', '34'])).
% 0.21/0.49  thf('36', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['8', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.21/0.49         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('split', [status(esa)], ['13'])).
% 0.21/0.49  thf('38', plain, (![X10 : $i]: ((k1_subset_1 @ X10) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['14', '32'])).
% 0.21/0.49  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['36', '41'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
