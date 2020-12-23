%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8HmcOscP8J

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 192 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  359 (1500 expanded)
%              Number of equality atoms :   39 (  64 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('2',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_xboole_0 @ ( k6_domain_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','18'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 != X10 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X10 ) )
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X10 ) )
     != ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X10 ) )
     != ( k1_tarski @ X10 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','18'])).

thf('28',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','18'])).

thf('29',plain,(
    ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t75_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
        = k1_xboole_0 )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ ( k2_tarski @ X13 @ X16 ) )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t75_zfmisc_1])).

thf('33',plain,(
    ! [X13: $i,X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X13 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('37',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['29','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8HmcOscP8J
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 88 iterations in 0.094s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(t6_tex_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.56           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.56                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.56              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.56                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.20/0.56  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X23 : $i, X24 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X23)
% 0.20/0.56          | ~ (m1_subset_1 @ X24 @ X23)
% 0.20/0.56          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.56        | (v1_xboole_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('4', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.20/0.56      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('5', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_k6_domain_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.56       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i]:
% 0.20/0.56         ((v1_xboole_0 @ X21)
% 0.20/0.56          | ~ (m1_subset_1 @ X22 @ X21)
% 0.20/0.56          | (m1_subset_1 @ (k6_domain_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21)))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.56        | (v1_xboole_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      ((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf(cc2_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.20/0.56          | ~ (v1_subset_1 @ X25 @ X26)
% 0.20/0.56          | (v1_xboole_0 @ X25)
% 0.20/0.56          | ~ (v1_zfmisc_1 @ X26)
% 0.20/0.56          | (v1_xboole_0 @ X26))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (((v1_xboole_0 @ sk_A)
% 0.20/0.56        | ~ (v1_zfmisc_1 @ sk_A)
% 0.20/0.56        | (v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B))
% 0.20/0.56        | ~ (v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf('12', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('13', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.56  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('16', plain, ((v1_xboole_0 @ (k6_domain_1 @ sk_A @ sk_B))),
% 0.20/0.56      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf(l13_xboole_0, axiom,
% 0.20/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.56  thf('18', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '18'])).
% 0.20/0.56  thf(t20_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.56         ( k1_tarski @ A ) ) <=>
% 0.20/0.56       ( ( A ) != ( B ) ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i]:
% 0.20/0.56         (((X11) != (X10))
% 0.20/0.56          | ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X10))
% 0.20/0.56              != (k1_tarski @ X11)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X10 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X10))
% 0.20/0.56           != (k1_tarski @ X10))),
% 0.20/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.56  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.56  thf(t100_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.56           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X10 : $i]:
% 0.20/0.56         ((k5_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X10))
% 0.20/0.56           != (k1_tarski @ X10))),
% 0.20/0.56      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '25'])).
% 0.20/0.56  thf('27', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '18'])).
% 0.20/0.56  thf('28', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '18'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.56  thf('30', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '18'])).
% 0.20/0.56  thf(t69_enumset1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.56  thf('31', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf(t75_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.56       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.20/0.56            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ X15 @ (k2_tarski @ X13 @ X16)) = (k1_xboole_0))
% 0.20/0.56          | ((X15) != (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t75_zfmisc_1])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X13 : $i, X16 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X13 @ X16)) = (k1_xboole_0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['31', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['30', '34'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('38', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['29', '37'])).
% 0.20/0.56  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
