%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lqtP9ngvxU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  425 ( 847 expanded)
%              Number of equality atoms :   42 (  71 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k2_subset_1 @ X20 )
      = X20 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('32',plain,(
    ! [X20: $i] :
      ( ( k2_subset_1 @ X20 )
      = X20 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('33',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X21 ) @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( k2_subset_1 @ X20 )
      = X20 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lqtP9ngvxU
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 78 iterations in 0.031s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(d3_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i]:
% 0.22/0.49         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf(t28_subset_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.22/0.49  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(l3_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X22 @ X23)
% 0.22/0.49          | (r2_hidden @ X22 @ X24)
% 0.22/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i]:
% 0.22/0.49         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.49  thf('6', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.49  thf(t28_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.49  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.49  thf(t100_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X6 @ X7)
% 0.22/0.49           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.49           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '12'])).
% 0.22/0.49  thf(t51_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.49       ( A ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 0.22/0.49           = (X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.22/0.49  thf(commutativity_k2_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.49  thf(l51_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X18 @ X19)) = (k2_xboole_0 @ X18 @ X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ (k3_xboole_0 @ X12 @ X13))
% 0.22/0.49           = (X12))),
% 0.22/0.49      inference('demod', [status(thm)], ['14', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.22/0.49         (k3_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['13', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.49  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '12'])).
% 0.22/0.49  thf(t39_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.22/0.49           = (k2_xboole_0 @ X10 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.22/0.49         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['25', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.22/0.49         != (k2_subset_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.49  thf('31', plain, (![X20 : $i]: ((k2_subset_1 @ X20) = (X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('32', plain, (![X20 : $i]: ((k2_subset_1 @ X20) = (X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('33', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.22/0.49  thf(dt_k2_subset_1, axiom,
% 0.22/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (![X21 : $i]: (m1_subset_1 @ (k2_subset_1 @ X21) @ (k1_zfmisc_1 @ X21))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.49  thf('35', plain, (![X20 : $i]: ((k2_subset_1 @ X20) = (X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('36', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.22/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.49  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(redefinition_k4_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.49       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.22/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 0.22/0.49          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['36', '39'])).
% 0.22/0.49  thf('41', plain, (((k2_xboole_0 @ sk_B @ sk_A) != (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['33', '40'])).
% 0.22/0.49  thf('42', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['29', '41'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
