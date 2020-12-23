%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GG0fJG0vAk

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:32 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 194 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  541 (1680 expanded)
%              Number of equality atoms :   59 ( 169 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X32 @ ( k3_subset_1 @ X31 @ X32 ) )
      | ( X32
        = ( k1_subset_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('23',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('28',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('42',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['25','40','41'])).

thf('43',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['23','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X23: $i] :
      ( ( k1_subset_1 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','43','44','45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['16','50'])).

thf('52',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('53',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['25','40'])).

thf('56',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GG0fJG0vAk
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 236 iterations in 0.072s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(t39_subset_1, conjecture,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.23/0.54         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i,B:$i]:
% 0.23/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.23/0.54            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.23/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(dt_k3_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      (![X27 : $i, X28 : $i]:
% 0.23/0.54         ((m1_subset_1 @ (k3_subset_1 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 0.23/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.54  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d5_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.54  thf('4', plain,
% 0.23/0.54      (![X25 : $i, X26 : $i]:
% 0.23/0.54         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.23/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['2', '5'])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      (![X25 : $i, X26 : $i]:
% 0.23/0.54         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.23/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.23/0.54         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.54  thf(t48_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X17 : $i, X18 : $i]:
% 0.23/0.54         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.23/0.54           = (k3_xboole_0 @ X17 @ X18))),
% 0.23/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.23/0.54         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.23/0.54  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(involutiveness_k3_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X29 : $i, X30 : $i]:
% 0.23/0.54         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 0.23/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.23/0.54      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.54  thf('16', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.23/0.54      inference('sup+', [status(thm)], ['10', '15'])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.54  thf(t38_subset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.54       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.23/0.54         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (![X31 : $i, X32 : $i]:
% 0.23/0.54         (~ (r1_tarski @ X32 @ (k3_subset_1 @ X31 @ X32))
% 0.23/0.54          | ((X32) = (k1_subset_1 @ X31))
% 0.23/0.54          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.23/0.54        | ~ (m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.54        | ((k4_xboole_0 @ sk_A @ sk_B) = (k1_subset_1 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.23/0.54        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.23/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.54      inference('split', [status(esa)], ['20'])).
% 0.23/0.54  thf('22', plain,
% 0.23/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 0.23/0.54         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.23/0.54  thf('24', plain,
% 0.23/0.54      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.23/0.54        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.23/0.54       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.54      inference('split', [status(esa)], ['24'])).
% 0.23/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.54  thf('26', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('split', [status(esa)], ['20'])).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.23/0.54  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.23/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('sup+', [status(thm)], ['28', '29'])).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      (![X25 : $i, X26 : $i]:
% 0.23/0.54         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.23/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.23/0.54         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.23/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.54      inference('split', [status(esa)], ['24'])).
% 0.23/0.54  thf('35', plain,
% 0.23/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.23/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.54  thf('36', plain,
% 0.23/0.54      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.23/0.54  thf('37', plain,
% 0.23/0.54      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.23/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.54  thf('38', plain,
% 0.23/0.54      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.23/0.54         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.54             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['32', '37'])).
% 0.23/0.54  thf(t36_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.23/0.54  thf('39', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.23/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.23/0.54  thf('40', plain,
% 0.23/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.23/0.54       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.23/0.54  thf('41', plain,
% 0.23/0.54      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.23/0.54       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.54      inference('split', [status(esa)], ['20'])).
% 0.23/0.54  thf('42', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['25', '40', '41'])).
% 0.23/0.54  thf('43', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['23', '42'])).
% 0.23/0.54  thf('44', plain,
% 0.23/0.54      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['2', '5'])).
% 0.23/0.54  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.54  thf('45', plain, (![X23 : $i]: ((k1_subset_1 @ X23) = (k1_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.23/0.54  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.23/0.54      inference('demod', [status(thm)], ['19', '43', '44', '45'])).
% 0.23/0.54  thf('47', plain,
% 0.23/0.54      (![X17 : $i, X18 : $i]:
% 0.23/0.54         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.23/0.54           = (k3_xboole_0 @ X17 @ X18))),
% 0.23/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.23/0.54  thf('48', plain,
% 0.23/0.54      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.54      inference('sup+', [status(thm)], ['46', '47'])).
% 0.23/0.54  thf(t3_boole, axiom,
% 0.23/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.54  thf('49', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.54  thf('50', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.23/0.54  thf('51', plain, (((sk_A) = (sk_B))),
% 0.23/0.54      inference('sup+', [status(thm)], ['16', '50'])).
% 0.23/0.54  thf('52', plain,
% 0.23/0.54      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.23/0.54         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('split', [status(esa)], ['24'])).
% 0.23/0.54  thf('53', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.54  thf('54', plain,
% 0.23/0.54      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.23/0.54  thf('55', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.54      inference('sat_resolution*', [status(thm)], ['25', '40'])).
% 0.23/0.54  thf('56', plain, (((sk_B) != (sk_A))),
% 0.23/0.54      inference('simpl_trail', [status(thm)], ['54', '55'])).
% 0.23/0.54  thf('57', plain, ($false),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['51', '56'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
