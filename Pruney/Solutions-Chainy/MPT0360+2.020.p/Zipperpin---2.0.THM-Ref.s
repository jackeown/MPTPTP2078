%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a2ePSXp9Q0

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:43 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 140 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  440 ( 982 expanded)
%              Number of equality atoms :   14 (  32 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X22 ) @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k2_subset_1 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X14 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X14 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('23',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( m1_subset_1 @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ( r1_tarski @ ( k3_subset_1 @ X25 @ X24 ) @ ( k3_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k3_subset_1 @ X27 @ X28 ) )
      | ( X28
        = ( k1_subset_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k3_subset_1 @ X27 @ X28 ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('46',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a2ePSXp9Q0
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.64/0.83  % Solved by: fo/fo7.sh
% 0.64/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.83  % done 746 iterations in 0.377s
% 0.64/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.64/0.83  % SZS output start Refutation
% 0.64/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.64/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.83  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.64/0.83  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.64/0.83  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.64/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.64/0.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.64/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.64/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.83  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.64/0.83  thf(dt_k2_subset_1, axiom,
% 0.64/0.83    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.64/0.83  thf('0', plain,
% 0.64/0.83      (![X22 : $i]: (m1_subset_1 @ (k2_subset_1 @ X22) @ (k1_zfmisc_1 @ X22))),
% 0.64/0.83      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.64/0.83  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.64/0.83  thf('1', plain, (![X21 : $i]: ((k2_subset_1 @ X21) = (X21))),
% 0.64/0.83      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.64/0.83  thf('2', plain, (![X22 : $i]: (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X22))),
% 0.64/0.83      inference('demod', [status(thm)], ['0', '1'])).
% 0.64/0.83  thf(d2_subset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( ( v1_xboole_0 @ A ) =>
% 0.64/0.83         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.64/0.83       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.64/0.83         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.64/0.83  thf('3', plain,
% 0.64/0.83      (![X17 : $i, X18 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X17 @ X18)
% 0.64/0.83          | (r2_hidden @ X17 @ X18)
% 0.64/0.83          | (v1_xboole_0 @ X18))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.64/0.83  thf('4', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.64/0.83          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.64/0.83  thf(fc1_subset_1, axiom,
% 0.64/0.83    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.64/0.83  thf('5', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.64/0.83      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.64/0.83  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.64/0.83      inference('clc', [status(thm)], ['4', '5'])).
% 0.64/0.83  thf(t40_subset_1, conjecture,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.83       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.64/0.83         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.64/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.64/0.83        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.83          ( ( ( r1_tarski @ B @ C ) & 
% 0.64/0.83              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.64/0.83            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.64/0.83    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.64/0.83  thf('7', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(t79_zfmisc_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( r1_tarski @ A @ B ) =>
% 0.64/0.83       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.64/0.83  thf('8', plain,
% 0.64/0.83      (![X14 : $i, X15 : $i]:
% 0.64/0.83         ((r1_tarski @ (k1_zfmisc_1 @ X14) @ (k1_zfmisc_1 @ X15))
% 0.64/0.83          | ~ (r1_tarski @ X14 @ X15))),
% 0.64/0.83      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.64/0.83  thf('9', plain,
% 0.64/0.83      ((r1_tarski @ (k1_zfmisc_1 @ sk_B) @ (k1_zfmisc_1 @ sk_C_1))),
% 0.64/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.64/0.83  thf(d3_tarski, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.64/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.64/0.83  thf('10', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.83         (~ (r2_hidden @ X0 @ X1)
% 0.64/0.83          | (r2_hidden @ X0 @ X2)
% 0.64/0.83          | ~ (r1_tarski @ X1 @ X2))),
% 0.64/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.64/0.83  thf('11', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_C_1))
% 0.64/0.83          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['9', '10'])).
% 0.64/0.83  thf('12', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_C_1))),
% 0.64/0.83      inference('sup-', [status(thm)], ['6', '11'])).
% 0.64/0.83  thf('13', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('14', plain,
% 0.64/0.83      (![X17 : $i, X18 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X17 @ X18)
% 0.64/0.83          | (r2_hidden @ X17 @ X18)
% 0.64/0.83          | (v1_xboole_0 @ X18))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.64/0.83  thf('15', plain,
% 0.64/0.83      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.64/0.83        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.64/0.83  thf('16', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.64/0.83      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.64/0.83  thf('17', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.83      inference('clc', [status(thm)], ['15', '16'])).
% 0.64/0.83  thf(l49_zfmisc_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.64/0.83  thf('18', plain,
% 0.64/0.83      (![X12 : $i, X13 : $i]:
% 0.64/0.83         ((r1_tarski @ X12 @ (k3_tarski @ X13)) | ~ (r2_hidden @ X12 @ X13))),
% 0.64/0.83      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.64/0.83  thf('19', plain, ((r1_tarski @ sk_C_1 @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.64/0.83  thf(t99_zfmisc_1, axiom,
% 0.64/0.83    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.64/0.83  thf('20', plain, (![X16 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X16)) = (X16))),
% 0.64/0.83      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.64/0.83  thf('21', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.64/0.83      inference('demod', [status(thm)], ['19', '20'])).
% 0.64/0.83  thf('22', plain,
% 0.64/0.83      (![X14 : $i, X15 : $i]:
% 0.64/0.83         ((r1_tarski @ (k1_zfmisc_1 @ X14) @ (k1_zfmisc_1 @ X15))
% 0.64/0.83          | ~ (r1_tarski @ X14 @ X15))),
% 0.64/0.83      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.64/0.83  thf('23', plain,
% 0.64/0.83      ((r1_tarski @ (k1_zfmisc_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.83      inference('sup-', [status(thm)], ['21', '22'])).
% 0.64/0.83  thf('24', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.83         (~ (r2_hidden @ X0 @ X1)
% 0.64/0.83          | (r2_hidden @ X0 @ X2)
% 0.64/0.83          | ~ (r1_tarski @ X1 @ X2))),
% 0.64/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.64/0.83  thf('25', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.64/0.83          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_C_1)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.64/0.83  thf('26', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.83      inference('sup-', [status(thm)], ['12', '25'])).
% 0.64/0.83  thf('27', plain,
% 0.64/0.83      (![X17 : $i, X18 : $i]:
% 0.64/0.83         (~ (r2_hidden @ X17 @ X18)
% 0.64/0.83          | (m1_subset_1 @ X17 @ X18)
% 0.64/0.83          | (v1_xboole_0 @ X18))),
% 0.64/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.64/0.83  thf(t7_boole, axiom,
% 0.64/0.83    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.64/0.83  thf('28', plain,
% 0.64/0.83      (![X10 : $i, X11 : $i]:
% 0.64/0.83         (~ (r2_hidden @ X10 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.64/0.83      inference('cnf', [status(esa)], [t7_boole])).
% 0.64/0.83  thf('29', plain,
% 0.64/0.83      (![X17 : $i, X18 : $i]:
% 0.64/0.83         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.64/0.83      inference('clc', [status(thm)], ['27', '28'])).
% 0.64/0.83  thf('30', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.83      inference('sup-', [status(thm)], ['26', '29'])).
% 0.64/0.83  thf('31', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(t31_subset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.83       ( ![C:$i]:
% 0.64/0.83         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.83           ( ( r1_tarski @ B @ C ) <=>
% 0.64/0.83             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.64/0.83  thf('32', plain,
% 0.64/0.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.64/0.83          | ~ (r1_tarski @ X26 @ X24)
% 0.64/0.83          | (r1_tarski @ (k3_subset_1 @ X25 @ X24) @ (k3_subset_1 @ X25 @ X26))
% 0.64/0.83          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.64/0.83      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.64/0.83  thf('33', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.64/0.83          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.64/0.83             (k3_subset_1 @ sk_A @ X0))
% 0.64/0.83          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.64/0.83      inference('sup-', [status(thm)], ['31', '32'])).
% 0.64/0.83  thf('34', plain,
% 0.64/0.83      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.64/0.83        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.64/0.83           (k3_subset_1 @ sk_A @ sk_B)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['30', '33'])).
% 0.64/0.83  thf('35', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('36', plain,
% 0.64/0.83      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.64/0.83      inference('demod', [status(thm)], ['34', '35'])).
% 0.64/0.83  thf('37', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(t1_xboole_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.64/0.83       ( r1_tarski @ A @ C ) ))).
% 0.64/0.83  thf('38', plain,
% 0.64/0.83      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.64/0.83         (~ (r1_tarski @ X7 @ X8)
% 0.64/0.83          | ~ (r1_tarski @ X8 @ X9)
% 0.64/0.83          | (r1_tarski @ X7 @ X9))),
% 0.64/0.83      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.64/0.83  thf('39', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((r1_tarski @ sk_B @ X0)
% 0.64/0.83          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['37', '38'])).
% 0.64/0.83  thf('40', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.64/0.83      inference('sup-', [status(thm)], ['36', '39'])).
% 0.64/0.83  thf(t38_subset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.83       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.64/0.83         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.64/0.83  thf('41', plain,
% 0.64/0.83      (![X27 : $i, X28 : $i]:
% 0.64/0.83         (~ (r1_tarski @ X28 @ (k3_subset_1 @ X27 @ X28))
% 0.64/0.83          | ((X28) = (k1_subset_1 @ X27))
% 0.64/0.83          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.64/0.83      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.64/0.83  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.64/0.83  thf('42', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.64/0.83      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.64/0.83  thf('43', plain,
% 0.64/0.83      (![X27 : $i, X28 : $i]:
% 0.64/0.83         (~ (r1_tarski @ X28 @ (k3_subset_1 @ X27 @ X28))
% 0.64/0.83          | ((X28) = (k1_xboole_0))
% 0.64/0.83          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.64/0.83      inference('demod', [status(thm)], ['41', '42'])).
% 0.64/0.83  thf('44', plain,
% 0.64/0.83      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))
% 0.64/0.83        | ((sk_B) = (k1_xboole_0)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['40', '43'])).
% 0.64/0.83  thf('45', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.64/0.83      inference('sup-', [status(thm)], ['26', '29'])).
% 0.64/0.83  thf('46', plain, (((sk_B) = (k1_xboole_0))),
% 0.64/0.83      inference('demod', [status(thm)], ['44', '45'])).
% 0.64/0.83  thf('47', plain, (((sk_B) != (k1_xboole_0))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('48', plain, ($false),
% 0.64/0.83      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.64/0.83  
% 0.64/0.83  % SZS output end Refutation
% 0.64/0.83  
% 0.64/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
