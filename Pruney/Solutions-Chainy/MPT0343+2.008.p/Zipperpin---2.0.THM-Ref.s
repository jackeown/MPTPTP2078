%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IH6Okk7HRa

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:37 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 221 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   22
%              Number of atoms          :  492 (1848 expanded)
%              Number of equality atoms :    9 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

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
    r1_tarski @ sk_C_3 @ sk_A ),
    inference(clc,[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( m1_subset_1 @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_3 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_C_3 )
      | ( r2_hidden @ X20 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X20 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_3 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_3 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,
    ( ( r1_tarski @ sk_C_3 @ sk_B_1 )
    | ( r1_tarski @ sk_C_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_C_3 @ sk_B_1 ),
    inference(simplify,[status(thm)],['29'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('32',plain,
    ( ( sk_C_3 = sk_B_1 )
    | ( r2_xboole_0 @ sk_C_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B_1 != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_xboole_0 @ sk_C_3 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('36',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_3 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_3 ) @ sk_A ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('54',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_C_3 ) @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_B_1 )
      | ( r2_hidden @ X20 @ sk_C_3 )
      | ~ ( m1_subset_1 @ X20 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_3 ) @ sk_C_3 )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_3 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('58',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_C_3 ) @ sk_C_3 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_xboole_0 @ X10 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('60',plain,(
    ~ ( r2_xboole_0 @ sk_C_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r2_xboole_0 @ sk_C_3 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IH6Okk7HRa
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:42:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.63  % Solved by: fo/fo7.sh
% 0.43/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.63  % done 273 iterations in 0.176s
% 0.43/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.63  % SZS output start Refutation
% 0.43/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.43/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.63  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.43/0.63  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.43/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.63  thf(d3_tarski, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.43/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.43/0.63  thf('0', plain,
% 0.43/0.63      (![X4 : $i, X6 : $i]:
% 0.43/0.63         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.43/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.63  thf(t8_subset_1, conjecture,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.63       ( ![C:$i]:
% 0.43/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.63           ( ( ![D:$i]:
% 0.43/0.63               ( ( m1_subset_1 @ D @ A ) =>
% 0.43/0.63                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.43/0.63             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.63    (~( ![A:$i,B:$i]:
% 0.43/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.63          ( ![C:$i]:
% 0.43/0.63            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.63              ( ( ![D:$i]:
% 0.43/0.63                  ( ( m1_subset_1 @ D @ A ) =>
% 0.43/0.63                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.43/0.63                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.43/0.63    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.43/0.63  thf('1', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(d2_subset_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.43/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.43/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.63  thf('2', plain,
% 0.43/0.63      (![X17 : $i, X18 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X17 @ X18)
% 0.43/0.63          | (r2_hidden @ X17 @ X18)
% 0.43/0.63          | (v1_xboole_0 @ X18))),
% 0.43/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.63  thf('3', plain,
% 0.43/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.63        | (r2_hidden @ sk_C_3 @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.63  thf(d1_zfmisc_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.43/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.43/0.63  thf('4', plain,
% 0.43/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X15 @ X14)
% 0.43/0.63          | (r1_tarski @ X15 @ X13)
% 0.43/0.63          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.43/0.63  thf('5', plain,
% 0.43/0.63      (![X13 : $i, X15 : $i]:
% 0.43/0.63         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['4'])).
% 0.43/0.63  thf('6', plain,
% 0.43/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_C_3 @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['3', '5'])).
% 0.43/0.63  thf('7', plain,
% 0.43/0.63      (![X4 : $i, X6 : $i]:
% 0.43/0.63         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.43/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.63  thf('8', plain,
% 0.43/0.63      (![X4 : $i, X6 : $i]:
% 0.43/0.63         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.43/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.63  thf('9', plain,
% 0.43/0.63      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.63  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.43/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.63  thf('11', plain,
% 0.43/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.63         (~ (r1_tarski @ X12 @ X13)
% 0.43/0.63          | (r2_hidden @ X12 @ X14)
% 0.43/0.63          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.43/0.63  thf('12', plain,
% 0.43/0.63      (![X12 : $i, X13 : $i]:
% 0.43/0.63         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 0.43/0.63      inference('simplify', [status(thm)], ['11'])).
% 0.43/0.63  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['10', '12'])).
% 0.43/0.63  thf(d1_xboole_0, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.63  thf('14', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.63  thf('15', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.43/0.63  thf('16', plain, ((r1_tarski @ sk_C_3 @ sk_A)),
% 0.43/0.63      inference('clc', [status(thm)], ['6', '15'])).
% 0.43/0.63  thf('17', plain,
% 0.43/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X3 @ X4)
% 0.43/0.63          | (r2_hidden @ X3 @ X5)
% 0.43/0.63          | ~ (r1_tarski @ X4 @ X5))),
% 0.43/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.63  thf('18', plain,
% 0.43/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.43/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.63  thf('19', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((r1_tarski @ sk_C_3 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['0', '18'])).
% 0.43/0.63  thf('20', plain,
% 0.43/0.63      (![X17 : $i, X18 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X17 @ X18)
% 0.43/0.63          | (m1_subset_1 @ X17 @ X18)
% 0.43/0.63          | (v1_xboole_0 @ X18))),
% 0.43/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.63  thf('21', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.63  thf('22', plain,
% 0.43/0.63      (![X17 : $i, X18 : $i]:
% 0.43/0.63         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.43/0.63      inference('clc', [status(thm)], ['20', '21'])).
% 0.43/0.63  thf('23', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.43/0.63          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_3) @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['19', '22'])).
% 0.43/0.63  thf('24', plain,
% 0.43/0.63      (![X20 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X20 @ sk_C_3)
% 0.46/0.63          | (r2_hidden @ X20 @ sk_B_1)
% 0.46/0.63          | ~ (m1_subset_1 @ X20 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r1_tarski @ sk_C_3 @ X0)
% 0.46/0.63          | (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_B_1)
% 0.46/0.63          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_C_3))),
% 0.46/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X4 : $i, X6 : $i]:
% 0.46/0.63         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_C @ X0 @ sk_C_3) @ sk_B_1)
% 0.46/0.63          | (r1_tarski @ sk_C_3 @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (![X4 : $i, X6 : $i]:
% 0.46/0.63         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (((r1_tarski @ sk_C_3 @ sk_B_1) | (r1_tarski @ sk_C_3 @ sk_B_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('30', plain, ((r1_tarski @ sk_C_3 @ sk_B_1)),
% 0.46/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.63  thf(d8_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.46/0.63       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X7 : $i, X9 : $i]:
% 0.46/0.63         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.46/0.63  thf('32', plain, ((((sk_C_3) = (sk_B_1)) | (r2_xboole_0 @ sk_C_3 @ sk_B_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.63  thf('33', plain, (((sk_B_1) != (sk_C_3))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('34', plain, ((r2_xboole_0 @ sk_C_3 @ sk_B_1)),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf(t6_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.46/0.63          ( ![C:$i]:
% 0.46/0.63            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (r2_xboole_0 @ X10 @ X11)
% 0.46/0.63          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.46/0.63  thf('36', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_3) @ sk_B_1)),
% 0.46/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.63  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X17 @ X18)
% 0.46/0.63          | (r2_hidden @ X17 @ X18)
% 0.46/0.63          | (v1_xboole_0 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.63        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (![X13 : $i, X15 : $i]:
% 0.46/0.63         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.63  thf('42', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (![X18 : $i, X19 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X19 @ X18)
% 0.46/0.63          | (v1_xboole_0 @ X19)
% 0.46/0.63          | ~ (v1_xboole_0 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.63  thf('45', plain, (((r1_tarski @ sk_B_1 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['41', '44'])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X4 : $i, X6 : $i]:
% 0.46/0.63         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.63  thf('49', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.46/0.63      inference('clc', [status(thm)], ['45', '48'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X3 @ X4)
% 0.46/0.63          | (r2_hidden @ X3 @ X5)
% 0.46/0.63          | ~ (r1_tarski @ X4 @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.63  thf('52', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_3) @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['36', '51'])).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i]:
% 0.46/0.63         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.46/0.63      inference('clc', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('54', plain, ((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_C_3) @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      (![X20 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X20 @ sk_B_1)
% 0.46/0.63          | (r2_hidden @ X20 @ sk_C_3)
% 0.46/0.63          | ~ (m1_subset_1 @ X20 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_3) @ sk_C_3)
% 0.46/0.64        | ~ (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_3) @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_3) @ sk_B_1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('58', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_C_3) @ sk_C_3)),
% 0.46/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]:
% 0.46/0.64         (~ (r2_xboole_0 @ X10 @ X11)
% 0.46/0.64          | ~ (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.46/0.64  thf('60', plain, (~ (r2_xboole_0 @ sk_C_3 @ sk_B_1)),
% 0.46/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.64  thf('61', plain, ((r2_xboole_0 @ sk_C_3 @ sk_B_1)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('62', plain, ($false), inference('demod', [status(thm)], ['60', '61'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
