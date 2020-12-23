%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UAT3M1R8yM

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:34 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 205 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  538 (1619 expanded)
%              Number of equality atoms :   63 ( 177 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r1_tarski @ X20 @ X18 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

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
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['4','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['4','19'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( ( k3_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('28',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('29',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('30',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','38'])).

thf('40',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('49',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['27','47','48'])).

thf('50',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['25','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','50'])).

thf('52',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['20','51','52'])).

thf('54',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('55',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('56',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['27','47'])).

thf('58',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UAT3M1R8yM
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:14:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.18/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.56  % Solved by: fo/fo7.sh
% 0.18/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.56  % done 382 iterations in 0.119s
% 0.18/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.56  % SZS output start Refutation
% 0.18/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.18/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.18/0.56  thf(t39_subset_1, conjecture,
% 0.18/0.56    (![A:$i,B:$i]:
% 0.18/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.56       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.18/0.56         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.18/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.56    (~( ![A:$i,B:$i]:
% 0.18/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.56          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.18/0.56            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.18/0.56    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.18/0.56  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.18/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.56  thf(d5_subset_1, axiom,
% 0.18/0.56    (![A:$i,B:$i]:
% 0.18/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.18/0.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.18/0.56  thf('1', plain,
% 0.18/0.56      (![X26 : $i, X27 : $i]:
% 0.18/0.56         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.18/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.18/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.18/0.56  thf('2', plain,
% 0.18/0.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.18/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.56  thf(t48_xboole_1, axiom,
% 0.18/0.56    (![A:$i,B:$i]:
% 0.18/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.18/0.56  thf('3', plain,
% 0.18/0.56      (![X15 : $i, X16 : $i]:
% 0.18/0.56         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.18/0.56           = (k3_xboole_0 @ X15 @ X16))),
% 0.18/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.18/0.56  thf('4', plain,
% 0.18/0.56      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.18/0.56         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.18/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.18/0.56  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.18/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.56  thf(d2_subset_1, axiom,
% 0.18/0.56    (![A:$i,B:$i]:
% 0.18/0.56     ( ( ( v1_xboole_0 @ A ) =>
% 0.18/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.18/0.56       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.18/0.56         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.18/0.56  thf('6', plain,
% 0.18/0.56      (![X22 : $i, X23 : $i]:
% 0.18/0.56         (~ (m1_subset_1 @ X22 @ X23)
% 0.18/0.56          | (r2_hidden @ X22 @ X23)
% 0.18/0.56          | (v1_xboole_0 @ X23))),
% 0.18/0.56      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.18/0.56  thf('7', plain,
% 0.18/0.56      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.18/0.56        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.18/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.56  thf(fc1_subset_1, axiom,
% 0.18/0.56    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.18/0.56  thf('8', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.18/0.56      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.18/0.56  thf('9', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.18/0.56      inference('clc', [status(thm)], ['7', '8'])).
% 0.18/0.56  thf(d1_zfmisc_1, axiom,
% 0.18/0.56    (![A:$i,B:$i]:
% 0.18/0.56     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.18/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.18/0.56  thf('10', plain,
% 0.18/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.18/0.56         (~ (r2_hidden @ X20 @ X19)
% 0.18/0.56          | (r1_tarski @ X20 @ X18)
% 0.18/0.56          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.18/0.56      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.18/0.56  thf('11', plain,
% 0.18/0.56      (![X18 : $i, X20 : $i]:
% 0.18/0.56         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 0.18/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.18/0.56  thf('12', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.18/0.56      inference('sup-', [status(thm)], ['9', '11'])).
% 0.18/0.56  thf(l32_xboole_1, axiom,
% 0.18/0.56    (![A:$i,B:$i]:
% 0.18/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.18/0.56  thf('13', plain,
% 0.18/0.56      (![X5 : $i, X7 : $i]:
% 0.18/0.56         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.18/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.56  thf('14', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.18/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.56  thf('15', plain,
% 0.18/0.56      (![X15 : $i, X16 : $i]:
% 0.18/0.56         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.18/0.56           = (k3_xboole_0 @ X15 @ X16))),
% 0.18/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.18/0.56  thf('16', plain,
% 0.18/0.56      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.18/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.18/0.56  thf(t3_boole, axiom,
% 0.18/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.56  thf('17', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.18/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.18/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.18/0.56  thf('18', plain,
% 0.18/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.18/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.18/0.56  thf('19', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.18/0.56      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.18/0.56  thf('20', plain,
% 0.18/0.56      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.18/0.56      inference('demod', [status(thm)], ['4', '19'])).
% 0.18/0.56  thf('21', plain,
% 0.18/0.56      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.18/0.56      inference('demod', [status(thm)], ['4', '19'])).
% 0.18/0.56  thf(t38_xboole_1, axiom,
% 0.18/0.56    (![A:$i,B:$i]:
% 0.18/0.56     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.18/0.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.18/0.56  thf('22', plain,
% 0.18/0.56      (![X12 : $i, X13 : $i]:
% 0.18/0.56         (((X12) = (k1_xboole_0))
% 0.18/0.56          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.18/0.56      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.18/0.56  thf('23', plain,
% 0.18/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.18/0.56        | ((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.18/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.18/0.56  thf('24', plain,
% 0.18/0.56      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.18/0.56        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.18/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.56  thf('25', plain,
% 0.18/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.18/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.18/0.56      inference('split', [status(esa)], ['24'])).
% 0.18/0.56  thf('26', plain,
% 0.18/0.56      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.18/0.56        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.18/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.56  thf('27', plain,
% 0.18/0.56      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.18/0.56       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.18/0.56      inference('split', [status(esa)], ['26'])).
% 0.18/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.18/0.56  thf('28', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.18/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.18/0.56  thf('29', plain,
% 0.18/0.56      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('split', [status(esa)], ['24'])).
% 0.18/0.56  thf('30', plain,
% 0.18/0.56      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.18/0.56  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.18/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.56  thf('32', plain,
% 0.18/0.56      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.18/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.18/0.56  thf('33', plain,
% 0.18/0.56      (![X26 : $i, X27 : $i]:
% 0.18/0.56         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.18/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.18/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.18/0.56  thf('34', plain,
% 0.18/0.56      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.18/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.18/0.56  thf(d10_xboole_0, axiom,
% 0.18/0.56    (![A:$i,B:$i]:
% 0.18/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.56  thf('35', plain,
% 0.18/0.56      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.18/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.56  thf('36', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.18/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.18/0.56  thf('37', plain,
% 0.18/0.56      (![X5 : $i, X7 : $i]:
% 0.18/0.56         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.18/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.18/0.56  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.18/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.18/0.56  thf('39', plain,
% 0.18/0.56      ((((k3_subset_1 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.18/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('demod', [status(thm)], ['34', '38'])).
% 0.18/0.56  thf('40', plain,
% 0.18/0.56      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.18/0.56  thf('41', plain,
% 0.18/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.18/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.18/0.56      inference('split', [status(esa)], ['26'])).
% 0.18/0.56  thf('42', plain,
% 0.18/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.18/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.18/0.56             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.18/0.56  thf('43', plain,
% 0.18/0.56      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.18/0.56  thf('44', plain,
% 0.18/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.18/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.18/0.56             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.18/0.56  thf('45', plain,
% 0.18/0.56      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.18/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.18/0.56             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('sup-', [status(thm)], ['39', '44'])).
% 0.18/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.56  thf('46', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.18/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.56  thf('47', plain,
% 0.18/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.18/0.56       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.18/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.18/0.56  thf('48', plain,
% 0.18/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.18/0.56       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.18/0.56      inference('split', [status(esa)], ['24'])).
% 0.18/0.56  thf('49', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.18/0.56      inference('sat_resolution*', [status(thm)], ['27', '47', '48'])).
% 0.18/0.56  thf('50', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)),
% 0.18/0.56      inference('simpl_trail', [status(thm)], ['25', '49'])).
% 0.18/0.56  thf('51', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.18/0.56      inference('demod', [status(thm)], ['23', '50'])).
% 0.18/0.56  thf('52', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.18/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.56  thf('53', plain, (((sk_A) = (sk_B))),
% 0.18/0.56      inference('demod', [status(thm)], ['20', '51', '52'])).
% 0.18/0.56  thf('54', plain,
% 0.18/0.56      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.18/0.56         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('split', [status(esa)], ['26'])).
% 0.18/0.56  thf('55', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.18/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.18/0.56  thf('56', plain,
% 0.18/0.56      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.18/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.18/0.56  thf('57', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.18/0.56      inference('sat_resolution*', [status(thm)], ['27', '47'])).
% 0.18/0.56  thf('58', plain, (((sk_B) != (sk_A))),
% 0.18/0.56      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.18/0.56  thf('59', plain, ($false),
% 0.18/0.56      inference('simplify_reflect-', [status(thm)], ['53', '58'])).
% 0.18/0.56  
% 0.18/0.56  % SZS output end Refutation
% 0.18/0.56  
% 0.18/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
