%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jX3hooHpSh

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:36 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   57 (  76 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  362 ( 618 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t8_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( m1_subset_1 @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_C_1 )
      | ( r2_hidden @ X17 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['14'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_B_1 )
      | ( r2_hidden @ X17 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_C_1 = sk_B_1 ),
    inference('sup+',[status(thm)],['19','35'])).

thf('37',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jX3hooHpSh
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:55:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 267 iterations in 0.232s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(d3_tarski, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.72  thf('0', plain,
% 0.50/0.72      (![X6 : $i, X8 : $i]:
% 0.50/0.72         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf(t8_subset_1, conjecture,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ![C:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72           ( ( ![D:$i]:
% 0.50/0.72               ( ( m1_subset_1 @ D @ A ) =>
% 0.50/0.72                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.50/0.72             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i,B:$i]:
% 0.50/0.72        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72          ( ![C:$i]:
% 0.50/0.72            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72              ( ( ![D:$i]:
% 0.50/0.72                  ( ( m1_subset_1 @ D @ A ) =>
% 0.50/0.72                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.50/0.72                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.50/0.72  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(l3_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.50/0.72  thf('2', plain,
% 0.50/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X14 @ X15)
% 0.50/0.72          | (r2_hidden @ X14 @ X16)
% 0.50/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.50/0.72      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.50/0.72  thf('3', plain,
% 0.50/0.72      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.72  thf('4', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['0', '3'])).
% 0.50/0.72  thf(d2_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( ( v1_xboole_0 @ A ) =>
% 0.50/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.50/0.72       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.50/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.72  thf('5', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X11 @ X12)
% 0.50/0.72          | (m1_subset_1 @ X11 @ X12)
% 0.50/0.72          | (v1_xboole_0 @ X12))),
% 0.50/0.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.50/0.72  thf(d1_xboole_0, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.50/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.72  thf('7', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i]:
% 0.50/0.72         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.50/0.72      inference('clc', [status(thm)], ['5', '6'])).
% 0.50/0.72  thf('8', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_C_1 @ X0)
% 0.50/0.72          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['4', '7'])).
% 0.50/0.72  thf('9', plain,
% 0.50/0.72      (![X17 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X17 @ sk_C_1)
% 0.50/0.72          | (r2_hidden @ X17 @ sk_B_1)
% 0.50/0.72          | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('10', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_C_1 @ X0)
% 0.50/0.72          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B_1)
% 0.50/0.72          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.72  thf('11', plain,
% 0.50/0.72      (![X6 : $i, X8 : $i]:
% 0.50/0.72         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('12', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B_1)
% 0.50/0.72          | (r1_tarski @ sk_C_1 @ X0))),
% 0.50/0.72      inference('clc', [status(thm)], ['10', '11'])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      (![X6 : $i, X8 : $i]:
% 0.50/0.72         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('14', plain,
% 0.50/0.72      (((r1_tarski @ sk_C_1 @ sk_B_1) | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.72  thf('15', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.50/0.72      inference('simplify', [status(thm)], ['14'])).
% 0.50/0.72  thf(t28_xboole_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.72  thf('16', plain,
% 0.50/0.72      (![X9 : $i, X10 : $i]:
% 0.50/0.72         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.50/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.72  thf('17', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.72  thf('18', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.72  thf('19', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.50/0.72      inference('demod', [status(thm)], ['17', '18'])).
% 0.50/0.72  thf('20', plain,
% 0.50/0.72      (![X6 : $i, X8 : $i]:
% 0.50/0.72         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('21', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X14 @ X15)
% 0.50/0.72          | (r2_hidden @ X14 @ X16)
% 0.50/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.50/0.72      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.50/0.72  thf('23', plain,
% 0.50/0.72      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['20', '23'])).
% 0.50/0.72  thf('25', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i]:
% 0.50/0.72         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.50/0.72      inference('clc', [status(thm)], ['5', '6'])).
% 0.50/0.72  thf('26', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B_1 @ X0)
% 0.50/0.72          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.72  thf('27', plain,
% 0.50/0.72      (![X17 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X17 @ sk_B_1)
% 0.50/0.72          | (r2_hidden @ X17 @ sk_C_1)
% 0.50/0.72          | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('28', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r1_tarski @ sk_B_1 @ X0)
% 0.50/0.72          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.50/0.72          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.72  thf('29', plain,
% 0.50/0.72      (![X6 : $i, X8 : $i]:
% 0.50/0.72         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('30', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.50/0.72          | (r1_tarski @ sk_B_1 @ X0))),
% 0.50/0.72      inference('clc', [status(thm)], ['28', '29'])).
% 0.50/0.72  thf('31', plain,
% 0.50/0.72      (![X6 : $i, X8 : $i]:
% 0.50/0.72         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.72  thf('32', plain,
% 0.50/0.72      (((r1_tarski @ sk_B_1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.72  thf('33', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.50/0.72      inference('simplify', [status(thm)], ['32'])).
% 0.50/0.72  thf('34', plain,
% 0.50/0.72      (![X9 : $i, X10 : $i]:
% 0.50/0.72         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.50/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.72  thf('35', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.72  thf('36', plain, (((sk_C_1) = (sk_B_1))),
% 0.50/0.72      inference('sup+', [status(thm)], ['19', '35'])).
% 0.50/0.72  thf('37', plain, (((sk_B_1) != (sk_C_1))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('38', plain, ($false),
% 0.50/0.72      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.50/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
