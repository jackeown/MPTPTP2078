%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l3lgAV5Bvn

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  65 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  296 ( 436 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X44 ) @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( k2_subset_1 @ X43 )
      = X43 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X44 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
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
    ! [X45: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t56_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ( ( A != k1_xboole_0 )
           => ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ A )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( ( A != k1_xboole_0 )
             => ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_subset_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X34 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X38 ) @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k1_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( m1_subset_1 @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('25',plain,(
    ! [X40: $i,X41: $i] :
      ( ( m1_subset_1 @ X40 @ X41 )
      | ~ ( r2_hidden @ X40 @ X41 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ~ ( m1_subset_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l3lgAV5Bvn
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:50:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 153 iterations in 0.061s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(dt_k2_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X44 : $i]: (m1_subset_1 @ (k2_subset_1 @ X44) @ (k1_zfmisc_1 @ X44))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.52  thf('1', plain, (![X43 : $i]: ((k2_subset_1 @ X43) = (X43))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.52  thf('2', plain, (![X44 : $i]: (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X44))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf(d2_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X40 : $i, X41 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X40 @ X41)
% 0.22/0.52          | (r2_hidden @ X40 @ X41)
% 0.22/0.52          | (v1_xboole_0 @ X41))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.22/0.52          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(fc1_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('5', plain, (![X45 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X45))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.52  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf(t56_subset_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.52           ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.52             ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.52          ( ![C:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.52              ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.52                ( m1_subset_1 @ ( k2_tarski @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t56_subset_1])).
% 0.22/0.52  thf('7', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X40 : $i, X41 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X40 @ X41)
% 0.22/0.52          | (r2_hidden @ X40 @ X41)
% 0.22/0.52          | (v1_xboole_0 @ X41))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.52  thf('9', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X40 : $i, X41 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X40 @ X41)
% 0.22/0.52          | (r2_hidden @ X40 @ X41)
% 0.22/0.52          | (v1_xboole_0 @ X41))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.52  thf('12', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf(t38_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X34 : $i, X36 : $i, X37 : $i]:
% 0.22/0.52         ((r1_tarski @ (k2_tarski @ X34 @ X36) @ X37)
% 0.22/0.52          | ~ (r2_hidden @ X36 @ X37)
% 0.22/0.52          | ~ (r2_hidden @ X34 @ X37))),
% 0.22/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf(t7_boole, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_boole])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_A)
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A) | (r1_tarski @ (k2_tarski @ sk_B @ sk_C_1) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.52  thf(t79_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.52       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X38 : $i, X39 : $i]:
% 0.22/0.52         ((r1_tarski @ (k1_zfmisc_1 @ X38) @ (k1_zfmisc_1 @ X39))
% 0.22/0.52          | ~ (r1_tarski @ X38 @ X39))),
% 0.22/0.52      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | (r1_tarski @ (k1_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1)) @ 
% 0.22/0.52           (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf(d3_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.52          | (r2_hidden @ X0 @ X2)
% 0.22/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ sk_A)
% 0.22/0.52          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (((r2_hidden @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52        | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X40 : $i, X41 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X40 @ X41)
% 0.22/0.52          | (m1_subset_1 @ X40 @ X41)
% 0.22/0.52          | (v1_xboole_0 @ X41))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_boole])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X40 : $i, X41 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X40 @ X41) | ~ (r2_hidden @ X40 @ X41))),
% 0.22/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | (m1_subset_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (~ (m1_subset_1 @ (k2_tarski @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('28', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf(l13_xboole_0, axiom,
% 0.22/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.52  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
