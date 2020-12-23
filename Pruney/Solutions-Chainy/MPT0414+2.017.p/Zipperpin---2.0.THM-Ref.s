%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0fXiBjBdOC

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 121 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  427 (1137 expanded)
%              Number of equality atoms :   11 (  33 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t44_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_C_2 )
      | ( r2_hidden @ X11 @ sk_B )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_C_2 @ sk_B ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ X0 )
      | ( X0 = sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,
    ( ( sk_B = sk_C_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf('21',plain,(
    sk_B != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ sk_B )
      | ( r2_hidden @ X11 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_2 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
    | ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['22','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B )
    | ( sk_B = sk_C_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('45',plain,(
    sk_B = sk_C_2 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0fXiBjBdOC
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 103 iterations in 0.091s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(t2_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.53       ( ( A ) = ( B ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         (((X5) = (X4))
% 0.21/0.53          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.21/0.53          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf(t44_setfam_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53           ( ( ![D:$i]:
% 0.21/0.53               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.53             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53          ( ![C:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53              ( ( ![D:$i]:
% 0.21/0.53                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.21/0.53                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('4', plain, ((r1_tarski @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_C_2 @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.53  thf(t1_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_C_2 @ X0)
% 0.21/0.53          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X11 @ sk_C_2)
% 0.21/0.53          | (r2_hidden @ X11 @ sk_B)
% 0.21/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_C_2 @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B)
% 0.21/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B) | (r1_tarski @ sk_C_2 @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (((r1_tarski @ sk_C_2 @ sk_B) | (r1_tarski @ sk_C_2 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain, ((r1_tarski @ sk_C_2 @ sk_B)),
% 0.21/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ X0)
% 0.21/0.53          | ((X0) = (sk_C_2))
% 0.21/0.53          | (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      ((((sk_B) = (sk_C_2)) | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B))),
% 0.21/0.53      inference('eq_fact', [status(thm)], ['19'])).
% 0.21/0.53  thf('21', plain, (((sk_B) != (sk_C_2))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('26', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_B @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_B @ X0)
% 0.21/0.53          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X11 @ sk_B)
% 0.21/0.53          | (r2_hidden @ X11 @ sk_C_2)
% 0.21/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_B @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_2)
% 0.21/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_2) | (r1_tarski @ sk_B @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((r1_tarski @ sk_B @ sk_C_2) | (r1_tarski @ sk_B @ sk_C_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 0.21/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_C_2)),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         (((X5) = (X4))
% 0.21/0.53          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.21/0.53          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B) | ((sk_B) = (sk_C_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B) @ sk_B)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('45', plain, (((sk_B) = (sk_C_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain, (((sk_B) != (sk_C_2))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('47', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
