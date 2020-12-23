%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1jWfDeYUmI

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:32 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   66 (  88 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  328 ( 560 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( ( k6_domain_1 @ X24 @ X25 )
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1jWfDeYUmI
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.52  % Solved by: fo/fo7.sh
% 0.36/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.52  % done 40 iterations in 0.020s
% 0.36/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.52  % SZS output start Refutation
% 0.36/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.36/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.36/0.52  thf(t6_tex_2, conjecture,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.52       ( ![B:$i]:
% 0.36/0.52         ( ( m1_subset_1 @ B @ A ) =>
% 0.36/0.52           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.36/0.52                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.36/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.52    (~( ![A:$i]:
% 0.36/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.52          ( ![B:$i]:
% 0.36/0.52            ( ( m1_subset_1 @ B @ A ) =>
% 0.36/0.52              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.36/0.52                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.36/0.52    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.36/0.52  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(dt_k6_domain_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.52  thf('1', plain,
% 0.36/0.52      (![X22 : $i, X23 : $i]:
% 0.36/0.52         ((v1_xboole_0 @ X22)
% 0.36/0.52          | ~ (m1_subset_1 @ X23 @ X22)
% 0.36/0.52          | (m1_subset_1 @ (k6_domain_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22)))),
% 0.36/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.36/0.52  thf('2', plain,
% 0.36/0.52      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.52        | (v1_xboole_0 @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.52  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.52  thf('4', plain,
% 0.36/0.52      (![X24 : $i, X25 : $i]:
% 0.36/0.52         ((v1_xboole_0 @ X24)
% 0.36/0.52          | ~ (m1_subset_1 @ X25 @ X24)
% 0.36/0.52          | ((k6_domain_1 @ X24 @ X25) = (k1_tarski @ X25)))),
% 0.36/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.52  thf('5', plain,
% 0.36/0.52      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.36/0.52        | (v1_xboole_0 @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.52  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.36/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.36/0.52  thf('8', plain,
% 0.36/0.52      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.52        | (v1_xboole_0 @ sk_A))),
% 0.36/0.52      inference('demod', [status(thm)], ['2', '7'])).
% 0.36/0.52  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.52      inference('clc', [status(thm)], ['8', '9'])).
% 0.36/0.52  thf(cc2_tex_2, axiom,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.36/0.52       ( ![B:$i]:
% 0.36/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.52           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.36/0.52  thf('11', plain,
% 0.36/0.52      (![X26 : $i, X27 : $i]:
% 0.36/0.52         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.36/0.52          | ~ (v1_subset_1 @ X26 @ X27)
% 0.36/0.52          | (v1_xboole_0 @ X26)
% 0.36/0.52          | ~ (v1_zfmisc_1 @ X27)
% 0.36/0.52          | (v1_xboole_0 @ X27))),
% 0.36/0.52      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.36/0.52  thf('12', plain,
% 0.36/0.52      (((v1_xboole_0 @ sk_A)
% 0.36/0.52        | ~ (v1_zfmisc_1 @ sk_A)
% 0.36/0.52        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.36/0.52        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.52  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.36/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.36/0.52  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.36/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.52  thf('17', plain,
% 0.36/0.52      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.36/0.52      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.36/0.52  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.36/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.36/0.52  thf(l13_xboole_0, axiom,
% 0.36/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.52  thf('20', plain,
% 0.36/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.52  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.52  thf(t4_subset_1, axiom,
% 0.36/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.52  thf('22', plain,
% 0.36/0.52      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.36/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.52  thf(t3_subset, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.52  thf('23', plain,
% 0.36/0.52      (![X16 : $i, X17 : $i]:
% 0.36/0.52         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.52  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.52  thf(t28_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.52  thf('25', plain,
% 0.36/0.52      (![X3 : $i, X4 : $i]:
% 0.36/0.52         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.36/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.52  thf('26', plain,
% 0.36/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.52  thf(t100_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.52  thf('27', plain,
% 0.36/0.52      (![X1 : $i, X2 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X1 @ X2)
% 0.36/0.52           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.52  thf('28', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.52           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.52  thf(t5_boole, axiom,
% 0.36/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.52  thf('29', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.36/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.52  thf('30', plain,
% 0.36/0.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.52  thf(t98_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.52  thf('31', plain,
% 0.36/0.52      (![X6 : $i, X7 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ X6 @ X7)
% 0.36/0.52           = (k5_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.52  thf('32', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.36/0.52  thf('33', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.36/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.52  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['32', '33'])).
% 0.36/0.52  thf(t49_zfmisc_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.36/0.52  thf('35', plain,
% 0.36/0.52      (![X11 : $i, X12 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.36/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.36/0.52  thf('36', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.52  thf('37', plain, ($false),
% 0.36/0.52      inference('simplify_reflect-', [status(thm)], ['21', '36'])).
% 0.36/0.52  
% 0.36/0.52  % SZS output end Refutation
% 0.36/0.52  
% 0.36/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
