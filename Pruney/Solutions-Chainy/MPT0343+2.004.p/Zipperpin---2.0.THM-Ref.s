%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m5AnW44PhJ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  333 ( 581 expanded)
%              Number of equality atoms :    6 (  14 expanded)
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

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_C_1 )
      | ( r2_hidden @ X16 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X16 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_B_1 )
      | ( r2_hidden @ X16 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X16 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['19','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m5AnW44PhJ
% 0.16/0.36  % Computer   : n012.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 14:05:52 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 248 iterations in 0.108s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(d3_tarski, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.54  thf('0', plain,
% 0.23/0.54      (![X4 : $i, X6 : $i]:
% 0.23/0.54         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.54  thf(t8_subset_1, conjecture,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ![C:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54           ( ( ![D:$i]:
% 0.23/0.54               ( ( m1_subset_1 @ D @ A ) =>
% 0.23/0.54                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.23/0.54             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i,B:$i]:
% 0.23/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54          ( ![C:$i]:
% 0.23/0.54            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54              ( ( ![D:$i]:
% 0.23/0.54                  ( ( m1_subset_1 @ D @ A ) =>
% 0.23/0.54                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.23/0.54                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.23/0.54  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(l3_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X13 @ X14)
% 0.23/0.54          | (r2_hidden @ X13 @ X15)
% 0.23/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.54  thf('4', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['0', '3'])).
% 0.23/0.54  thf(d2_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (![X10 : $i, X11 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X10 @ X11)
% 0.23/0.54          | (m1_subset_1 @ X10 @ X11)
% 0.23/0.54          | (v1_xboole_0 @ X11))),
% 0.23/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.54  thf(d1_xboole_0, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      (![X10 : $i, X11 : $i]:
% 0.23/0.54         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.23/0.54      inference('clc', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_tarski @ sk_C_1 @ X0)
% 0.23/0.54          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '7'])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X16 @ sk_C_1)
% 0.23/0.54          | (r2_hidden @ X16 @ sk_B_1)
% 0.23/0.54          | ~ (m1_subset_1 @ X16 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_tarski @ sk_C_1 @ X0)
% 0.23/0.54          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B_1)
% 0.23/0.54          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (![X4 : $i, X6 : $i]:
% 0.23/0.54         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B_1)
% 0.23/0.54          | (r1_tarski @ sk_C_1 @ X0))),
% 0.23/0.54      inference('clc', [status(thm)], ['10', '11'])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X4 : $i, X6 : $i]:
% 0.23/0.54         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (((r1_tarski @ sk_C_1 @ sk_B_1) | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.54  thf('15', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.23/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.23/0.54  thf(d10_xboole_0, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X7 : $i, X9 : $i]:
% 0.23/0.54         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.23/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.54  thf('17', plain, ((~ (r1_tarski @ sk_B_1 @ sk_C_1) | ((sk_B_1) = (sk_C_1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain, (((sk_B_1) != (sk_C_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('19', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X4 : $i, X6 : $i]:
% 0.23/0.54         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.54  thf('21', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('22', plain,
% 0.23/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X13 @ X14)
% 0.23/0.54          | (r2_hidden @ X13 @ X15)
% 0.23/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.23/0.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['20', '23'])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      (![X10 : $i, X11 : $i]:
% 0.23/0.54         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.23/0.54      inference('clc', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf('26', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_tarski @ sk_B_1 @ X0)
% 0.23/0.54          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X16 @ sk_B_1)
% 0.23/0.54          | (r2_hidden @ X16 @ sk_C_1)
% 0.23/0.54          | ~ (m1_subset_1 @ X16 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_tarski @ sk_B_1 @ X0)
% 0.23/0.54          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.23/0.54          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (![X4 : $i, X6 : $i]:
% 0.23/0.54         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)
% 0.23/0.54          | (r1_tarski @ sk_B_1 @ X0))),
% 0.23/0.54      inference('clc', [status(thm)], ['28', '29'])).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      (![X4 : $i, X6 : $i]:
% 0.23/0.54         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      (((r1_tarski @ sk_B_1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.54  thf('33', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.23/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.23/0.54  thf('34', plain, ($false), inference('demod', [status(thm)], ['19', '33'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
