%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S0wUhcTIU3

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:23 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   49 (  68 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  307 ( 507 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( X16
        = ( k6_domain_1 @ X16 @ ( sk_B @ X16 ) ) )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('4',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( m1_subset_1 @ ( sk_B @ X16 ) @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['25','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['2','27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S0wUhcTIU3
% 0.16/0.38  % Computer   : n008.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 10:39:30 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 78 iterations in 0.046s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.24/0.50  thf(t2_tex_2, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.24/0.50       ( ![B:$i]:
% 0.24/0.50         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.24/0.50           ( r1_tarski @ A @ B ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.24/0.50          ( ![B:$i]:
% 0.24/0.50            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.24/0.50              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.24/0.50  thf('0', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.50  thf('2', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.24/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf(d1_tex_2, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.50       ( ( v1_zfmisc_1 @ A ) <=>
% 0.24/0.50         ( ?[B:$i]:
% 0.24/0.50           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X16 : $i]:
% 0.24/0.50         (~ (v1_zfmisc_1 @ X16)
% 0.24/0.50          | ((X16) = (k6_domain_1 @ X16 @ (sk_B @ X16)))
% 0.24/0.50          | (v1_xboole_0 @ X16))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X16 : $i]:
% 0.24/0.50         (~ (v1_zfmisc_1 @ X16)
% 0.24/0.50          | (m1_subset_1 @ (sk_B @ X16) @ X16)
% 0.24/0.50          | (v1_xboole_0 @ X16))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.24/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X14 : $i, X15 : $i]:
% 0.24/0.50         ((v1_xboole_0 @ X14)
% 0.24/0.50          | ~ (m1_subset_1 @ X15 @ X14)
% 0.24/0.50          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.24/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((v1_xboole_0 @ X0)
% 0.24/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.24/0.50          | (v1_xboole_0 @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.24/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | (v1_xboole_0 @ X0))),
% 0.24/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.50  thf('8', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.24/0.50          | (v1_xboole_0 @ X0)
% 0.24/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | (v1_xboole_0 @ X0)
% 0.24/0.50          | ~ (v1_zfmisc_1 @ X0))),
% 0.24/0.50      inference('sup+', [status(thm)], ['3', '7'])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | (v1_xboole_0 @ X0)
% 0.24/0.50          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.24/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | (v1_xboole_0 @ X0)
% 0.24/0.50          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.24/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.24/0.50  thf(t17_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.24/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.24/0.50  thf(l3_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      (![X9 : $i, X10 : $i]:
% 0.24/0.50         (((X10) = (k1_tarski @ X9))
% 0.24/0.50          | ((X10) = (k1_xboole_0))
% 0.24/0.50          | ~ (r1_tarski @ X10 @ (k1_tarski @ X9)))),
% 0.24/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.24/0.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.50  thf('15', plain,
% 0.24/0.50      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.24/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.24/0.50  thf('16', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.24/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.24/0.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.24/0.50      inference('sup+', [status(thm)], ['13', '16'])).
% 0.24/0.50  thf('18', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r1_tarski @ X0 @ X1)
% 0.24/0.50          | (v1_xboole_0 @ X0)
% 0.24/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | ((k3_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X1) = (k1_xboole_0)))),
% 0.24/0.50      inference('sup+', [status(thm)], ['10', '17'])).
% 0.24/0.50  thf('19', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 0.24/0.50          | (v1_xboole_0 @ X0)
% 0.24/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | (v1_xboole_0 @ X0)
% 0.24/0.50          | (r1_tarski @ X0 @ X1))),
% 0.24/0.50      inference('sup+', [status(thm)], ['9', '18'])).
% 0.24/0.50  thf('20', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]:
% 0.24/0.50         ((r1_tarski @ X0 @ X1)
% 0.24/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.24/0.50          | (v1_xboole_0 @ X0)
% 0.24/0.50          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.24/0.50  thf('21', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('22', plain,
% 0.24/0.50      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.24/0.50        | (v1_xboole_0 @ sk_A)
% 0.24/0.50        | ~ (v1_zfmisc_1 @ sk_A))),
% 0.24/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.50  thf('23', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.50  thf('24', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('25', plain,
% 0.24/0.50      ((((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A))),
% 0.24/0.50      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.24/0.50  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('27', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.24/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.24/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.50  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.50  thf('29', plain, ($false),
% 0.24/0.50      inference('demod', [status(thm)], ['2', '27', '28'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
