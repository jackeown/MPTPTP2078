%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RP0N0X2bY6

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 145 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  428 (1184 expanded)
%              Number of equality atoms :   41 ( 122 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X17: $i] :
      ( ( k2_subset_1 @ X17 )
      = X17 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','18','19'])).

thf('21',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['21','24'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('29',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,(
    ! [X17: $i] :
      ( ( k2_subset_1 @ X17 )
      = X17 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','18'])).

thf('36',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('42',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r1_tarski @ X12 @ X10 )
      | ( X11
       != ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('44',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['37','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RP0N0X2bY6
% 0.12/0.36  % Computer   : n008.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 16:48:15 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 104 iterations in 0.040s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(t39_subset_1, conjecture,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.48       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.23/0.48         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i,B:$i]:
% 0.23/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.48          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.23/0.48            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.23/0.48        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.23/0.48         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.48      inference('split', [status(esa)], ['0'])).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.23/0.48        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.23/0.48       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.48      inference('split', [status(esa)], ['2'])).
% 0.23/0.48  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.48  thf('4', plain, (![X17 : $i]: ((k2_subset_1 @ X17) = (X17))),
% 0.23/0.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.48  thf('5', plain,
% 0.23/0.48      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('split', [status(esa)], ['0'])).
% 0.23/0.48  thf('6', plain, ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.48  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('8', plain,
% 0.23/0.48      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.23/0.48         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.23/0.48  thf(d5_subset_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.48  thf('9', plain,
% 0.23/0.48      (![X18 : $i, X19 : $i]:
% 0.23/0.48         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.23/0.48          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.23/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.48  thf('10', plain,
% 0.23/0.48      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.23/0.48         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.48  thf('11', plain,
% 0.23/0.48      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.48  thf('12', plain,
% 0.23/0.48      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.23/0.48         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.48      inference('split', [status(esa)], ['2'])).
% 0.23/0.48  thf('13', plain,
% 0.23/0.48      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.23/0.48         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.48             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.48  thf('14', plain,
% 0.23/0.48      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.48  thf('15', plain,
% 0.23/0.48      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.23/0.48         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.48             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.48  thf('16', plain,
% 0.23/0.48      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.23/0.48         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.48             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup-', [status(thm)], ['10', '15'])).
% 0.23/0.48  thf(t36_xboole_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.23/0.48  thf('17', plain,
% 0.23/0.48      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.23/0.48      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.23/0.48  thf('18', plain,
% 0.23/0.48      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.23/0.48       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.48  thf('19', plain,
% 0.23/0.48      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.23/0.48       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.48      inference('split', [status(esa)], ['0'])).
% 0.23/0.48  thf('20', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.48      inference('sat_resolution*', [status(thm)], ['3', '18', '19'])).
% 0.23/0.48  thf('21', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)),
% 0.23/0.48      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.23/0.48  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('23', plain,
% 0.23/0.48      (![X18 : $i, X19 : $i]:
% 0.23/0.48         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.23/0.48          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.23/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.48  thf('24', plain,
% 0.23/0.48      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.48  thf('25', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.23/0.48      inference('demod', [status(thm)], ['21', '24'])).
% 0.23/0.48  thf(t44_xboole_1, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i]:
% 0.23/0.48     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.23/0.48       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.23/0.48  thf('26', plain,
% 0.23/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.48         ((r1_tarski @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 0.23/0.48          | ~ (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X8))),
% 0.23/0.48      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.23/0.48  thf('27', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.23/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.48  thf(idempotence_k2_xboole_0, axiom,
% 0.23/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.23/0.48  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.23/0.48  thf('29', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.48  thf(d10_xboole_0, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.48  thf('30', plain,
% 0.23/0.48      (![X1 : $i, X3 : $i]:
% 0.23/0.48         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.23/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.48  thf('31', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.48  thf('32', plain,
% 0.23/0.48      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.23/0.48         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('split', [status(esa)], ['2'])).
% 0.23/0.48  thf('33', plain, (![X17 : $i]: ((k2_subset_1 @ X17) = (X17))),
% 0.23/0.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.48  thf('34', plain,
% 0.23/0.48      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.48  thf('35', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.48      inference('sat_resolution*', [status(thm)], ['3', '18'])).
% 0.23/0.48  thf('36', plain, (((sk_B) != (sk_A))),
% 0.23/0.48      inference('simpl_trail', [status(thm)], ['34', '35'])).
% 0.23/0.48  thf('37', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.23/0.48      inference('simplify_reflect-', [status(thm)], ['31', '36'])).
% 0.23/0.48  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(d2_subset_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.48  thf('39', plain,
% 0.23/0.48      (![X14 : $i, X15 : $i]:
% 0.23/0.48         (~ (m1_subset_1 @ X14 @ X15)
% 0.23/0.48          | (r2_hidden @ X14 @ X15)
% 0.23/0.48          | (v1_xboole_0 @ X15))),
% 0.23/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.48  thf('40', plain,
% 0.23/0.48      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.48        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.23/0.48  thf(fc1_subset_1, axiom,
% 0.23/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.48  thf('41', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.23/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.48  thf('42', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.48      inference('clc', [status(thm)], ['40', '41'])).
% 0.23/0.48  thf(d1_zfmisc_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.23/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.23/0.48  thf('43', plain,
% 0.23/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.48         (~ (r2_hidden @ X12 @ X11)
% 0.23/0.48          | (r1_tarski @ X12 @ X10)
% 0.23/0.48          | ((X11) != (k1_zfmisc_1 @ X10)))),
% 0.23/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.48  thf('44', plain,
% 0.23/0.48      (![X10 : $i, X12 : $i]:
% 0.23/0.48         ((r1_tarski @ X12 @ X10) | ~ (r2_hidden @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.23/0.48      inference('simplify', [status(thm)], ['43'])).
% 0.23/0.48  thf('45', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.23/0.48      inference('sup-', [status(thm)], ['42', '44'])).
% 0.23/0.48  thf('46', plain, ($false), inference('demod', [status(thm)], ['37', '45'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
