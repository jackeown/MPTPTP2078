%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OWVBLyc71L

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  247 ( 369 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t7_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                   => ( r2_hidden @ D @ C ) ) )
             => ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_B_1 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_B_1 )
      | ( r2_hidden @ X14 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X14 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OWVBLyc71L
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 158 iterations in 0.084s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.57  thf(t7_subset_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57           ( ( ![D:$i]:
% 0.38/0.57               ( ( m1_subset_1 @ D @ A ) =>
% 0.38/0.57                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.38/0.57             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i]:
% 0.38/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57          ( ![C:$i]:
% 0.38/0.57            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57              ( ( ![D:$i]:
% 0.38/0.57                  ( ( m1_subset_1 @ D @ A ) =>
% 0.38/0.57                    ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.38/0.57                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t7_subset_1])).
% 0.38/0.57  thf('0', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d3_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X4 : $i, X6 : $i]:
% 0.38/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d2_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.38/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.38/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X10 @ X11)
% 0.38/0.57          | (r2_hidden @ X10 @ X11)
% 0.38/0.57          | (v1_xboole_0 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.57        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf(fc1_subset_1, axiom,
% 0.38/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.57  thf('5', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.38/0.57  thf('6', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf(l49_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]:
% 0.38/0.57         ((r1_tarski @ X7 @ (k3_tarski @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 0.38/0.57      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.38/0.57  thf('8', plain, ((r1_tarski @ sk_B_1 @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf(t99_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.38/0.57  thf('9', plain, (![X9 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X9)) = (X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.38/0.57  thf('10', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X3 @ X4)
% 0.38/0.57          | (r2_hidden @ X3 @ X5)
% 0.38/0.57          | ~ (r1_tarski @ X4 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X10 @ X11)
% 0.38/0.57          | (m1_subset_1 @ X10 @ X11)
% 0.38/0.57          | (v1_xboole_0 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.57  thf(d1_xboole_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X10 : $i, X11 : $i]:
% 0.38/0.57         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.38/0.57      inference('clc', [status(thm)], ['14', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ sk_B_1 @ X0)
% 0.38/0.57          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X14 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X14 @ sk_B_1)
% 0.38/0.57          | (r2_hidden @ X14 @ sk_C_1)
% 0.38/0.57          | ~ (m1_subset_1 @ X14 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r1_tarski @ sk_B_1 @ X0)
% 0.38/0.57          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.38/0.57          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X4 : $i, X6 : $i]:
% 0.38/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.38/0.57          | (r1_tarski @ sk_B_1 @ X0))),
% 0.38/0.57      inference('clc', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X4 : $i, X6 : $i]:
% 0.38/0.57         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (((r1_tarski @ sk_B_1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('24', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.38/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.57  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
