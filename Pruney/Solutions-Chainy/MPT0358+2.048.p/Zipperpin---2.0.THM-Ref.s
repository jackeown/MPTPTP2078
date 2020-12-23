%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.511aOoptsL

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 151 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  508 (1169 expanded)
%              Number of equality atoms :   57 ( 123 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X26 @ ( k3_subset_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6
        = ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('15',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('24',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('30',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['21','31','32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['19','33'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['2','41'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('43',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X26 @ ( k3_subset_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = ( k3_subset_1 @ X27 @ ( k1_subset_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('47',plain,(
    ! [X21: $i] :
      ( ( k2_subset_1 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('48',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('49',plain,(
    ! [X27: $i] :
      ( X27
      = ( k3_subset_1 @ X27 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','49'])).

thf('51',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['42','50'])).

thf('52',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('53',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['21','31'])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.511aOoptsL
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:28:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 84 iterations in 0.039s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(t38_subset_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.50         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.50            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.22/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X25 : $i, X26 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X26 @ (k3_subset_1 @ X26 @ X25)) = (X25))
% 0.22/0.50          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.22/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d5_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d2_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X17 @ X18)
% 0.22/0.50          | (r2_hidden @ X17 @ X18)
% 0.22/0.50          | (v1_xboole_0 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.50        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf(fc1_subset_1, axiom,
% 0.22/0.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.50  thf('9', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.50  thf('10', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf(d1_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X15 @ X14)
% 0.22/0.50          | (r1_tarski @ X15 @ X13)
% 0.22/0.50          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X13 : $i, X15 : $i]:
% 0.22/0.50         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf('13', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '12'])).
% 0.22/0.50  thf(t45_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.50       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         (((X6) = (k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))
% 0.22/0.50          | ~ (r1_tarski @ X5 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (((sk_A) = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.22/0.50        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('17', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((((sk_B) = (k1_xboole_0))
% 0.22/0.50        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.22/0.50        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.22/0.50       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['20'])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('22', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('23', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.22/0.50        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.50      inference('split', [status(esa)], ['24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['23', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.50         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['20'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.50         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.22/0.50             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['23', '25'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.50         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.22/0.50             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.50       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.50       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['24'])).
% 0.22/0.50  thf('33', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['21', '31', '32'])).
% 0.22/0.50  thf('34', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['19', '33'])).
% 0.22/0.50  thf(t12_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.50         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.22/0.50         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.22/0.50  thf('40', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup+', [status(thm)], ['15', '39'])).
% 0.22/0.50  thf('41', plain, (((k3_subset_1 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '40'])).
% 0.22/0.50  thf('42', plain, (((k3_subset_1 @ sk_A @ sk_A) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '41'])).
% 0.22/0.50  thf(t4_subset_1, axiom,
% 0.22/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X25 : $i, X26 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X26 @ (k3_subset_1 @ X26 @ X25)) = (X25))
% 0.22/0.50          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.22/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf(t22_subset_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (![X27 : $i]:
% 0.22/0.50         ((k2_subset_1 @ X27) = (k3_subset_1 @ X27 @ (k1_subset_1 @ X27)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.22/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.50  thf('47', plain, (![X21 : $i]: ((k2_subset_1 @ X21) = (X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.50  thf('48', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.50  thf('49', plain, (![X27 : $i]: ((X27) = (k3_subset_1 @ X27 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.22/0.50  thf('50', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['45', '49'])).
% 0.22/0.50  thf('51', plain, (((k1_xboole_0) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '50'])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.22/0.50         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.50      inference('split', [status(esa)], ['20'])).
% 0.22/0.50  thf('53', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.50  thf('55', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['21', '31'])).
% 0.22/0.50  thf('56', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['54', '55'])).
% 0.22/0.50  thf('57', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['51', '56'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
