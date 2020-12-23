%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.30GOOuwTMK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  70 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  309 ( 504 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ ( k3_tarski @ X12 ) )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X6 ) )
      | ( r2_hidden @ X3 @ X6 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['20','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['26','27'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
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
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.30GOOuwTMK
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 61 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(t50_subset_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.48               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.20/0.48                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.48                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.20/0.48                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 0.20/0.48  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d2_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X14 @ X15)
% 0.20/0.48          | (r2_hidden @ X14 @ X15)
% 0.20/0.48          | (v1_xboole_0 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.48        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(fc1_subset_1, axiom,
% 0.20/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('3', plain, (![X19 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.48  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(l49_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         ((r1_tarski @ X11 @ (k3_tarski @ X12)) | ~ (r2_hidden @ X11 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.48  thf('6', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(t99_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.48  thf('7', plain, (![X13 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X13)) = (X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.48  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(t28_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.48  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.48  thf(t100_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.48           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['10', '13'])).
% 0.20/0.48  thf('15', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X14 @ X15)
% 0.20/0.48          | (r2_hidden @ X14 @ X15)
% 0.20/0.48          | (v1_xboole_0 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.48  thf('17', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(t1_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.48       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.48         ((r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X6))
% 0.20/0.48          | (r2_hidden @ X3 @ X6)
% 0.20/0.48          | ~ (r2_hidden @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ sk_A)
% 0.20/0.48          | (r2_hidden @ sk_C @ X0)
% 0.20/0.48          | (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.20/0.48        | (r2_hidden @ sk_C @ sk_B)
% 0.20/0.48        | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('sup+', [status(thm)], ['14', '19'])).
% 0.20/0.48  thf('21', plain, (~ (r2_hidden @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d5_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]:
% 0.20/0.48         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.20/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, (~ (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.48  thf('26', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['20', '25'])).
% 0.20/0.48  thf('27', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf(l13_xboole_0, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.48  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
