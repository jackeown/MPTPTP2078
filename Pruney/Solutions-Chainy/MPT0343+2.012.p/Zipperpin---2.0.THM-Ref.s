%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.szurIZpCAV

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 174 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  431 (2066 expanded)
%              Number of equality atoms :    6 (  64 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ X16 @ X14 )
      | ( r2_hidden @ ( sk_D @ X14 @ X16 @ X15 ) @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_A ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ X16 @ X14 )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X16 @ X15 ) @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B_1 @ X0 @ sk_A ) @ sk_A )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_B_1 @ sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_C_1 )
      | ( r2_hidden @ X17 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ sk_C_1 @ sk_A ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_D @ sk_B_1 @ sk_C_1 @ sk_A ) @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B_1 @ sk_C_1 @ sk_A ) @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ ( sk_D @ X14 @ X16 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_1 @ X0 @ sk_A ) @ sk_B_1 )
      | ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['19'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('22',plain,
    ( ( sk_C_1 = sk_B_1 )
    | ( r2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('26',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_C_1 ) @ sk_A ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_B_1 )
      | ( r2_hidden @ X17 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_C_1 ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('38',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('40',plain,(
    ~ ( r2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.szurIZpCAV
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:39:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 183 iterations in 0.107s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.57  thf(t8_subset_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ![C:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57           ( ( ![D:$i]:
% 0.22/0.57               ( ( m1_subset_1 @ D @ A ) =>
% 0.22/0.57                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.57             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i]:
% 0.22/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57          ( ![C:$i]:
% 0.22/0.57            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57              ( ( ![D:$i]:
% 0.22/0.57                  ( ( m1_subset_1 @ D @ A ) =>
% 0.22/0.57                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.57                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.22/0.57  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t7_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ![C:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57           ( ( ![D:$i]:
% 0.22/0.57               ( ( m1_subset_1 @ D @ A ) =>
% 0.22/0.57                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.57             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.22/0.57          | (r1_tarski @ X16 @ X14)
% 0.22/0.57          | (r2_hidden @ (sk_D @ X14 @ X16 @ X15) @ X16)
% 0.22/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.57          | (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_A) @ X0)
% 0.22/0.57          | (r1_tarski @ X0 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (((r1_tarski @ sk_C_1 @ sk_B_1)
% 0.22/0.57        | (r2_hidden @ (sk_D @ sk_B_1 @ sk_C_1 @ sk_A) @ sk_C_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.57  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('6', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.22/0.57          | (r1_tarski @ X16 @ X14)
% 0.22/0.57          | (m1_subset_1 @ (sk_D @ X14 @ X16 @ X15) @ X15)
% 0.22/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.57          | (m1_subset_1 @ (sk_D @ sk_B_1 @ X0 @ sk_A) @ sk_A)
% 0.22/0.57          | (r1_tarski @ X0 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (((r1_tarski @ sk_C_1 @ sk_B_1)
% 0.22/0.57        | (m1_subset_1 @ (sk_D @ sk_B_1 @ sk_C_1 @ sk_A) @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X17 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X17 @ sk_C_1)
% 0.22/0.57          | (r2_hidden @ X17 @ sk_B_1)
% 0.22/0.57          | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      (((r1_tarski @ sk_C_1 @ sk_B_1)
% 0.22/0.57        | (r2_hidden @ (sk_D @ sk_B_1 @ sk_C_1 @ sk_A) @ sk_B_1)
% 0.22/0.57        | ~ (r2_hidden @ (sk_D @ sk_B_1 @ sk_C_1 @ sk_A) @ sk_C_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (((r1_tarski @ sk_C_1 @ sk_B_1)
% 0.22/0.57        | (r2_hidden @ (sk_D @ sk_B_1 @ sk_C_1 @ sk_A) @ sk_B_1)
% 0.22/0.57        | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '11'])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (((r2_hidden @ (sk_D @ sk_B_1 @ sk_C_1 @ sk_A) @ sk_B_1)
% 0.22/0.57        | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.22/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.57  thf('14', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.22/0.57          | (r1_tarski @ X16 @ X14)
% 0.22/0.57          | ~ (r2_hidden @ (sk_D @ X14 @ X16 @ X15) @ X14)
% 0.22/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.57          | ~ (r2_hidden @ (sk_D @ sk_B_1 @ X0 @ sk_A) @ sk_B_1)
% 0.22/0.57          | (r1_tarski @ X0 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (((r1_tarski @ sk_C_1 @ sk_B_1)
% 0.22/0.57        | (r1_tarski @ sk_C_1 @ sk_B_1)
% 0.22/0.57        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.57  thf('18', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (((r1_tarski @ sk_C_1 @ sk_B_1) | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.22/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.57  thf('20', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.22/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.57  thf(d8_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.22/0.57       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X3 : $i, X5 : $i]:
% 0.22/0.57         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.57      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.22/0.57  thf('22', plain, ((((sk_C_1) = (sk_B_1)) | (r2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.57  thf('23', plain, (((sk_B_1) != (sk_C_1))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('24', plain, ((r2_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.57  thf(t6_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.22/0.57          ( ![C:$i]:
% 0.22/0.57            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i]:
% 0.22/0.57         (~ (r2_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.22/0.57      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.22/0.57  thf('26', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_C_1) @ sk_B_1)),
% 0.22/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.57  thf('27', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(l3_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X11 @ X12)
% 0.22/0.57          | (r2_hidden @ X11 @ X13)
% 0.22/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.57  thf('30', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.57  thf(d2_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X8 @ X9)
% 0.22/0.57          | (m1_subset_1 @ X8 @ X9)
% 0.22/0.57          | (v1_xboole_0 @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.57  thf(d1_xboole_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.22/0.57      inference('clc', [status(thm)], ['31', '32'])).
% 0.22/0.57  thf('34', plain, ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['30', '33'])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X17 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X17 @ sk_B_1)
% 0.22/0.57          | (r2_hidden @ X17 @ sk_C_1)
% 0.22/0.57          | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      (((r2_hidden @ (sk_C @ sk_B_1 @ sk_C_1) @ sk_C_1)
% 0.22/0.57        | ~ (r2_hidden @ (sk_C @ sk_B_1 @ sk_C_1) @ sk_B_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.57  thf('37', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_C_1) @ sk_B_1)),
% 0.22/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.57  thf('38', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_C_1) @ sk_C_1)),
% 0.22/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i]:
% 0.22/0.57         (~ (r2_xboole_0 @ X6 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.22/0.57  thf('40', plain, (~ (r2_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.22/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.57  thf('41', plain, ((r2_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.22/0.57  thf('42', plain, ($false), inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
