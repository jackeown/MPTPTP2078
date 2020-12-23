%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uTTQKnsxHI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:35 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 106 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  396 ( 711 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_zfmisc_1 @ X18 )
      | ( X19 = X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference(clc,[status(thm)],['20','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_tarski @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['7','31'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( sk_B @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_zfmisc_1 @ X18 )
      | ( X19 = X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( sk_B @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( v1_xboole_0 @ X8 )
      | ( v1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( sk_B @ X0 )
        = X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uTTQKnsxHI
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 114 iterations in 0.063s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.35/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.35/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.52  thf(t6_tex_2, conjecture,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( m1_subset_1 @ B @ A ) =>
% 0.35/0.52           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.35/0.52                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i]:
% 0.35/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.52          ( ![B:$i]:
% 0.35/0.52            ( ( m1_subset_1 @ B @ A ) =>
% 0.35/0.52              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.35/0.52                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.35/0.52  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('1', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      (![X16 : $i, X17 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ X16)
% 0.35/0.52          | ~ (m1_subset_1 @ X17 @ X16)
% 0.35/0.52          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      ((((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.35/0.52        | (v1_xboole_0 @ sk_A))),
% 0.35/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.52  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('6', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.35/0.52      inference('clc', [status(thm)], ['4', '5'])).
% 0.35/0.52  thf('7', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.35/0.52      inference('demod', [status(thm)], ['1', '6'])).
% 0.35/0.52  thf('8', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(dt_k6_domain_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      (![X14 : $i, X15 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ X14)
% 0.35/0.52          | ~ (m1_subset_1 @ X15 @ X14)
% 0.35/0.52          | (m1_subset_1 @ (k6_domain_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14)))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.35/0.52        | (v1_xboole_0 @ sk_A))),
% 0.35/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.52  thf('11', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      ((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.35/0.52  thf(t3_subset, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      (![X11 : $i, X12 : $i]:
% 0.35/0.52         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.52  thf('14', plain, ((r1_tarski @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.35/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.52  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.35/0.52      inference('clc', [status(thm)], ['4', '5'])).
% 0.35/0.52  thf('16', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.35/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.35/0.52  thf(t1_tex_2, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.35/0.52           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.35/0.52  thf('17', plain,
% 0.35/0.52      (![X18 : $i, X19 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ X18)
% 0.35/0.52          | ~ (v1_zfmisc_1 @ X18)
% 0.35/0.52          | ((X19) = (X18))
% 0.35/0.52          | ~ (r1_tarski @ X19 @ X18)
% 0.35/0.52          | (v1_xboole_0 @ X19))),
% 0.35/0.52      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.35/0.52  thf('18', plain,
% 0.35/0.52      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.35/0.52        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.35/0.52        | ~ (v1_zfmisc_1 @ sk_A)
% 0.35/0.52        | (v1_xboole_0 @ sk_A))),
% 0.35/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.52  thf('19', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('20', plain,
% 0.35/0.52      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.35/0.52        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.35/0.52        | (v1_xboole_0 @ sk_A))),
% 0.35/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.52  thf(t8_boole, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.35/0.52  thf('21', plain,
% 0.35/0.52      (![X1 : $i, X2 : $i]:
% 0.35/0.52         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t8_boole])).
% 0.35/0.52  thf(t1_boole, axiom,
% 0.35/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.52  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.35/0.52  thf(t49_zfmisc_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.35/0.52  thf('23', plain,
% 0.35/0.52      (![X6 : $i, X7 : $i]:
% 0.35/0.52         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.35/0.52  thf('24', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.52  thf('25', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (((X0) != (k1_xboole_0))
% 0.35/0.52          | ~ (v1_xboole_0 @ X0)
% 0.35/0.52          | ~ (v1_xboole_0 @ (k1_tarski @ X1)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['21', '24'])).
% 0.35/0.52  thf('26', plain,
% 0.35/0.52      (![X1 : $i]:
% 0.35/0.52         (~ (v1_xboole_0 @ (k1_tarski @ X1)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.35/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.35/0.52  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.52  thf('28', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X1))),
% 0.35/0.52      inference('simplify_reflect+', [status(thm)], ['26', '27'])).
% 0.35/0.52  thf('29', plain, (((v1_xboole_0 @ sk_A) | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.35/0.52      inference('clc', [status(thm)], ['20', '28'])).
% 0.35/0.52  thf('30', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('31', plain, (((k1_tarski @ sk_B_1) = (sk_A))),
% 0.35/0.52      inference('clc', [status(thm)], ['29', '30'])).
% 0.35/0.52  thf('32', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.35/0.52      inference('demod', [status(thm)], ['7', '31'])).
% 0.35/0.52  thf(rc3_subset_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ?[B:$i]:
% 0.35/0.52       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.35/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.35/0.52  thf('33', plain,
% 0.35/0.52      (![X10 : $i]: (m1_subset_1 @ (sk_B @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.35/0.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.35/0.52  thf('34', plain,
% 0.35/0.52      (![X11 : $i, X12 : $i]:
% 0.35/0.52         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.52  thf('35', plain, (![X0 : $i]: (r1_tarski @ (sk_B @ X0) @ X0)),
% 0.35/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.52  thf('36', plain,
% 0.35/0.52      (![X18 : $i, X19 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ X18)
% 0.35/0.52          | ~ (v1_zfmisc_1 @ X18)
% 0.35/0.52          | ((X19) = (X18))
% 0.35/0.52          | ~ (r1_tarski @ X19 @ X18)
% 0.35/0.52          | (v1_xboole_0 @ X19))),
% 0.35/0.52      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.35/0.52  thf('37', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ (sk_B @ X0))
% 0.35/0.52          | ((sk_B @ X0) = (X0))
% 0.35/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.35/0.52          | (v1_xboole_0 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.52  thf('38', plain,
% 0.35/0.52      (![X10 : $i]: (m1_subset_1 @ (sk_B @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.35/0.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.35/0.52  thf(cc2_subset_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.52           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 0.35/0.52  thf('39', plain,
% 0.35/0.52      (![X8 : $i, X9 : $i]:
% 0.35/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.35/0.52          | ~ (v1_xboole_0 @ X8)
% 0.35/0.52          | (v1_subset_1 @ X8 @ X9)
% 0.35/0.52          | (v1_xboole_0 @ X9))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc2_subset_1])).
% 0.35/0.52  thf('40', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ X0)
% 0.35/0.52          | (v1_subset_1 @ (sk_B @ X0) @ X0)
% 0.35/0.52          | ~ (v1_xboole_0 @ (sk_B @ X0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.35/0.52  thf('41', plain, (![X10 : $i]: ~ (v1_subset_1 @ (sk_B @ X10) @ X10)),
% 0.35/0.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.35/0.52  thf('42', plain,
% 0.35/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ (sk_B @ X0)) | (v1_xboole_0 @ X0))),
% 0.35/0.52      inference('clc', [status(thm)], ['40', '41'])).
% 0.35/0.52  thf('43', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ X0)
% 0.35/0.52          | ~ (v1_zfmisc_1 @ X0)
% 0.35/0.52          | ((sk_B @ X0) = (X0))
% 0.35/0.52          | (v1_xboole_0 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['37', '42'])).
% 0.35/0.52  thf('44', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((sk_B @ X0) = (X0)) | ~ (v1_zfmisc_1 @ X0) | (v1_xboole_0 @ X0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.35/0.52  thf('45', plain, (![X10 : $i]: ~ (v1_subset_1 @ (sk_B @ X10) @ X10)),
% 0.35/0.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.35/0.52  thf('46', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_subset_1 @ X0 @ X0) | (v1_xboole_0 @ X0) | ~ (v1_zfmisc_1 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.35/0.52  thf('47', plain, ((~ (v1_zfmisc_1 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.35/0.52      inference('sup-', [status(thm)], ['32', '46'])).
% 0.35/0.52  thf('48', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('49', plain, ((v1_xboole_0 @ sk_A)),
% 0.35/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.35/0.52  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.35/0.52  
% 0.35/0.52  % SZS output end Refutation
% 0.35/0.52  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
