%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iYB2OaP6T0

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 174 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  431 (2066 expanded)
%              Number of equality atoms :    6 (  64 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( r1_tarski @ X15 @ X13 )
      | ( r2_hidden @ ( sk_D @ X13 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( r1_tarski @ X15 @ X13 )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X15 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_C_1 )
      | ( r2_hidden @ X16 @ sk_B )
      | ~ ( m1_subset_1 @ X16 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C_1 @ sk_A ) @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ ( sk_D @ X13 @ X15 @ X14 ) @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('22',plain,
    ( ( sk_C_1 = sk_B )
    | ( r2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('26',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['26','29'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( m1_subset_1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_B )
      | ( r2_hidden @ X16 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X16 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('38',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('40',plain,(
    ~ ( r2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iYB2OaP6T0
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 81 iterations in 0.033s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.48  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(t8_subset_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48           ( ( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.48                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.48             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48          ( ![C:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48              ( ( ![D:$i]:
% 0.20/0.48                  ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.48                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.48                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.20/0.48  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t7_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48           ( ( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.48                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.48             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.20/0.48          | (r1_tarski @ X15 @ X13)
% 0.20/0.48          | (r2_hidden @ (sk_D @ X13 @ X15 @ X14) @ X15)
% 0.20/0.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.48          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0)
% 0.20/0.48          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.20/0.48        | (r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ sk_A) @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.20/0.48          | (r1_tarski @ X15 @ X13)
% 0.20/0.48          | (m1_subset_1 @ (sk_D @ X13 @ X15 @ X14) @ X14)
% 0.20/0.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.48          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.20/0.48          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.20/0.48        | (m1_subset_1 @ (sk_D @ sk_B @ sk_C_1 @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X16 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X16 @ sk_C_1)
% 0.20/0.48          | (r2_hidden @ X16 @ sk_B)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.20/0.48        | (r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ sk_A) @ sk_B)
% 0.20/0.48        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ sk_A) @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.20/0.48        | (r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ sk_A) @ sk_B)
% 0.20/0.48        | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (((r2_hidden @ (sk_D @ sk_B @ sk_C_1 @ sk_A) @ sk_B)
% 0.20/0.48        | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.20/0.48          | (r1_tarski @ X15 @ X13)
% 0.20/0.48          | ~ (r2_hidden @ (sk_D @ X13 @ X15 @ X14) @ X13)
% 0.20/0.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.48          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B)
% 0.20/0.48          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((r1_tarski @ sk_C_1 @ sk_B)
% 0.20/0.48        | (r1_tarski @ sk_C_1 @ sk_B)
% 0.20/0.48        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf('18', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((r1_tarski @ sk_C_1 @ sk_B) | (r1_tarski @ sk_C_1 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.20/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.48  thf(d8_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.48       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i]:
% 0.20/0.48         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.48  thf('22', plain, ((((sk_C_1) = (sk_B)) | (r2_xboole_0 @ sk_C_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain, (((sk_B) != (sk_C_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain, ((r2_xboole_0 @ sk_C_1 @ sk_B)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf(t6_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.20/0.48          ( ![C:$i]:
% 0.20/0.48            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (r2_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.48  thf('26', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(l3_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X10 @ X11)
% 0.20/0.48          | (r2_hidden @ X10 @ X12)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.48  thf(d2_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.48          | (m1_subset_1 @ X7 @ X8)
% 0.20/0.48          | (v1_xboole_0 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.48  thf(t7_boole, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_boole])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.20/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, ((m1_subset_1 @ (sk_C @ sk_B @ sk_C_1) @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X16 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X16 @ sk_B)
% 0.20/0.48          | (r2_hidden @ X16 @ sk_C_1)
% 0.20/0.48          | ~ (m1_subset_1 @ X16 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)
% 0.20/0.48        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('38', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_C_1)),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (r2_xboole_0 @ X3 @ X4) | ~ (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.48  thf('40', plain, (~ (r2_xboole_0 @ sk_C_1 @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain, ((r2_xboole_0 @ sk_C_1 @ sk_B)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('42', plain, ($false), inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
