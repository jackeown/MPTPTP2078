%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eQPWvgKPUR

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:36 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 113 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  475 ( 904 expanded)
%              Number of equality atoms :   10 (  30 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_tarski @ X13 @ X11 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('18',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_C_2 )
      | ( r2_hidden @ X18 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_1 )
    | ( r1_tarski @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( sk_B_1 = sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_B_1 )
      | ( r2_hidden @ X18 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_2 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['36','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eQPWvgKPUR
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 520 iterations in 0.299s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.75  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.54/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.75  thf(d3_tarski, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf(t8_subset_1, conjecture,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.75       ( ![C:$i]:
% 0.54/0.75         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.75           ( ( ![D:$i]:
% 0.54/0.75               ( ( m1_subset_1 @ D @ A ) =>
% 0.54/0.75                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.54/0.75             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i]:
% 0.54/0.75        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.75          ( ![C:$i]:
% 0.54/0.75            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.75              ( ( ![D:$i]:
% 0.54/0.75                  ( ( m1_subset_1 @ D @ A ) =>
% 0.54/0.75                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.54/0.75                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.54/0.75  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(d2_subset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( v1_xboole_0 @ A ) =>
% 0.54/0.75         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.54/0.75       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.75         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X15 @ X16)
% 0.54/0.75          | (r2_hidden @ X15 @ X16)
% 0.54/0.75          | (v1_xboole_0 @ X16))),
% 0.54/0.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.75  thf(d1_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.54/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.54/0.75  thf('4', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X13 @ X12)
% 0.54/0.75          | (r1_tarski @ X13 @ X11)
% 0.54/0.75          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X11 : $i, X13 : $i]:
% 0.54/0.75         ((r1_tarski @ X13 @ X11) | ~ (r2_hidden @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['4'])).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_C_2 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['3', '5'])).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.75         (~ (r1_tarski @ X10 @ X11)
% 0.54/0.75          | (r2_hidden @ X10 @ X12)
% 0.54/0.75          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i]:
% 0.54/0.75         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.54/0.75      inference('simplify', [status(thm)], ['7'])).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['6', '8'])).
% 0.54/0.75  thf(d10_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('11', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.54/0.75      inference('simplify', [status(thm)], ['10'])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i]:
% 0.54/0.75         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.54/0.75      inference('simplify', [status(thm)], ['7'])).
% 0.54/0.75  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.75  thf(d1_xboole_0, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.75  thf('15', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('16', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('clc', [status(thm)], ['9', '15'])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      (![X11 : $i, X13 : $i]:
% 0.54/0.75         ((r1_tarski @ X13 @ X11) | ~ (r2_hidden @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['4'])).
% 0.54/0.75  thf('18', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 0.54/0.75      inference('sup-', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X3 @ X4)
% 0.54/0.75          | (r2_hidden @ X3 @ X5)
% 0.54/0.75          | ~ (r1_tarski @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ sk_C_2 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['0', '20'])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X15 @ X16)
% 0.54/0.75          | (m1_subset_1 @ X15 @ X16)
% 0.54/0.75          | (v1_xboole_0 @ X16))),
% 0.54/0.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.54/0.75      inference('clc', [status(thm)], ['22', '23'])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ sk_C_2 @ X0)
% 0.54/0.75          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['21', '24'])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      (![X18 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X18 @ sk_C_2)
% 0.54/0.75          | (r2_hidden @ X18 @ sk_B_1)
% 0.54/0.75          | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ sk_C_2 @ X0)
% 0.54/0.75          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_1)
% 0.54/0.75          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 0.54/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_1)
% 0.54/0.75          | (r1_tarski @ sk_C_2 @ X0))),
% 0.54/0.75      inference('clc', [status(thm)], ['27', '28'])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (((r1_tarski @ sk_C_2 @ sk_B_1) | (r1_tarski @ sk_C_2 @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['29', '30'])).
% 0.54/0.75  thf('32', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 0.54/0.75      inference('simplify', [status(thm)], ['31'])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (![X7 : $i, X9 : $i]:
% 0.54/0.75         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('34', plain, ((~ (r1_tarski @ sk_B_1 @ sk_C_2) | ((sk_B_1) = (sk_C_2)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('35', plain, (((sk_B_1) != (sk_C_2))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('36', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('38', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X15 @ X16)
% 0.54/0.75          | (r2_hidden @ X15 @ X16)
% 0.54/0.75          | (v1_xboole_0 @ X16))),
% 0.54/0.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.54/0.75  thf('40', plain,
% 0.54/0.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      (![X11 : $i, X13 : $i]:
% 0.54/0.75         ((r1_tarski @ X13 @ X11) | ~ (r2_hidden @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['4'])).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['40', '41'])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X3 @ X4)
% 0.54/0.75          | (r2_hidden @ X3 @ X5)
% 0.54/0.75          | ~ (r1_tarski @ X4 @ X5))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.54/0.75          | (r2_hidden @ X0 @ sk_A)
% 0.54/0.75          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.75  thf('45', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | (r2_hidden @ X0 @ sk_A))),
% 0.54/0.75      inference('clc', [status(thm)], ['44', '45'])).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['37', '46'])).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.54/0.75      inference('clc', [status(thm)], ['22', '23'])).
% 0.54/0.75  thf('49', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ sk_B_1 @ X0)
% 0.54/0.75          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      (![X18 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X18 @ sk_B_1)
% 0.54/0.75          | (r2_hidden @ X18 @ sk_C_2)
% 0.54/0.75          | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('51', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ sk_B_1 @ X0)
% 0.54/0.75          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_2)
% 0.54/0.75          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['49', '50'])).
% 0.54/0.75  thf('52', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('53', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_2)
% 0.54/0.75          | (r1_tarski @ sk_B_1 @ X0))),
% 0.54/0.75      inference('clc', [status(thm)], ['51', '52'])).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      (((r1_tarski @ sk_B_1 @ sk_C_2) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('56', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.54/0.75      inference('simplify', [status(thm)], ['55'])).
% 0.54/0.75  thf('57', plain, ($false), inference('demod', [status(thm)], ['36', '56'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
