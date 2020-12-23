%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7WRY3p1N2E

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:19 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 121 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  431 ( 838 expanded)
%              Number of equality atoms :   62 ( 107 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X4 @ X3 ) )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X5 @ k1_xboole_0 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X17 ) @ X18 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','16'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X21: $i] :
      ( ~ ( v1_zfmisc_1 @ X21 )
      | ( X21
        = ( k6_domain_1 @ X21 @ ( sk_B_1 @ X21 ) ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('19',plain,(
    ! [X21: $i] :
      ( ~ ( v1_zfmisc_1 @ X21 )
      | ( m1_subset_1 @ ( sk_B_1 @ X21 ) @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X4 @ X3 ) )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('25',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = X15 )
      | ( ( k1_tarski @ X16 )
       != ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = X15 )
      | ( ( k1_tarski @ X16 )
       != ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
       != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','16'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['17','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7WRY3p1N2E
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:02:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 117 iterations in 0.069s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.55  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.23/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.23/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.23/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.55  thf(t1_tex_2, conjecture,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.55       ( ![B:$i]:
% 0.23/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.23/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i]:
% 0.23/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.55          ( ![B:$i]:
% 0.23/0.55            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.23/0.55              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.23/0.55  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(t1_boole, axiom,
% 0.23/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.55  thf('1', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.23/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.23/0.55  thf(l51_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.55  thf('2', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.23/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.55  thf('3', plain,
% 0.23/0.55      (![X5 : $i]: ((k3_tarski @ (k2_tarski @ X5 @ k1_xboole_0)) = (X5))),
% 0.23/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.55  thf(d1_xboole_0, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.55  thf('4', plain,
% 0.23/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.55  thf(l1_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.23/0.55  thf('5', plain,
% 0.23/0.55      (![X9 : $i, X11 : $i]:
% 0.23/0.55         ((r1_tarski @ (k1_tarski @ X9) @ X11) | ~ (r2_hidden @ X9 @ X11))),
% 0.23/0.55      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.23/0.55  thf('6', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.55  thf(t12_xboole_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.55  thf('7', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i]:
% 0.23/0.55         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.23/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.23/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i]:
% 0.23/0.55         (((k3_tarski @ (k2_tarski @ X4 @ X3)) = (X3))
% 0.23/0.55          | ~ (r1_tarski @ X4 @ X3))),
% 0.23/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.55  thf('10', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ X0)
% 0.23/0.55          | ((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)) = (X0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['6', '9'])).
% 0.23/0.55  thf('11', plain,
% 0.23/0.55      ((((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))
% 0.23/0.55        | (v1_xboole_0 @ k1_xboole_0))),
% 0.23/0.55      inference('sup+', [status(thm)], ['3', '10'])).
% 0.23/0.55  thf('12', plain,
% 0.23/0.55      (![X5 : $i]: ((k3_tarski @ (k2_tarski @ X5 @ k1_xboole_0)) = (X5))),
% 0.23/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.55  thf(t49_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.23/0.55  thf('13', plain,
% 0.23/0.55      (![X17 : $i, X18 : $i]:
% 0.23/0.55         ((k2_xboole_0 @ (k1_tarski @ X17) @ X18) != (k1_xboole_0))),
% 0.23/0.55      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.23/0.55  thf('14', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.23/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.55  thf('15', plain,
% 0.23/0.55      (![X17 : $i, X18 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ (k1_tarski @ X17) @ X18)) != (k1_xboole_0))),
% 0.23/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.55  thf('16', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['12', '15'])).
% 0.23/0.55  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['11', '16'])).
% 0.23/0.55  thf(d1_tex_2, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.55       ( ( v1_zfmisc_1 @ A ) <=>
% 0.23/0.55         ( ?[B:$i]:
% 0.23/0.55           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.23/0.55  thf('18', plain,
% 0.23/0.55      (![X21 : $i]:
% 0.23/0.55         (~ (v1_zfmisc_1 @ X21)
% 0.23/0.55          | ((X21) = (k6_domain_1 @ X21 @ (sk_B_1 @ X21)))
% 0.23/0.55          | (v1_xboole_0 @ X21))),
% 0.23/0.55      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.23/0.55  thf('19', plain,
% 0.23/0.55      (![X21 : $i]:
% 0.23/0.55         (~ (v1_zfmisc_1 @ X21)
% 0.23/0.55          | (m1_subset_1 @ (sk_B_1 @ X21) @ X21)
% 0.23/0.55          | (v1_xboole_0 @ X21))),
% 0.23/0.55      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.23/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.55  thf('20', plain,
% 0.23/0.55      (![X19 : $i, X20 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ X19)
% 0.23/0.55          | ~ (m1_subset_1 @ X20 @ X19)
% 0.23/0.55          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.23/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.55  thf('21', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((v1_xboole_0 @ X0)
% 0.23/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.55          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.23/0.55          | (v1_xboole_0 @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.55  thf('22', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.23/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.55          | (v1_xboole_0 @ X0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.23/0.55  thf('23', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('24', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i]:
% 0.23/0.55         (((k3_tarski @ (k2_tarski @ X4 @ X3)) = (X3))
% 0.23/0.55          | ~ (r1_tarski @ X4 @ X3))),
% 0.23/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.55  thf('25', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B_2)) = (sk_B_2))),
% 0.23/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.55  thf(t44_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.55          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.23/0.55          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.23/0.55  thf('26', plain,
% 0.23/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.55         (((X14) = (k1_xboole_0))
% 0.23/0.55          | ((X15) = (k1_xboole_0))
% 0.23/0.55          | ((X14) = (X15))
% 0.23/0.55          | ((k1_tarski @ X16) != (k2_xboole_0 @ X14 @ X15)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.23/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.55  thf('28', plain,
% 0.23/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.55         (((X14) = (k1_xboole_0))
% 0.23/0.55          | ((X15) = (k1_xboole_0))
% 0.23/0.55          | ((X14) = (X15))
% 0.23/0.55          | ((k1_tarski @ X16) != (k3_tarski @ (k2_tarski @ X14 @ X15))))),
% 0.23/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.23/0.55  thf('29', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k1_tarski @ X0) != (sk_B_2))
% 0.23/0.55          | ((sk_A) = (sk_B_2))
% 0.23/0.55          | ((sk_B_2) = (k1_xboole_0))
% 0.23/0.55          | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['25', '28'])).
% 0.23/0.55  thf('30', plain, (((sk_A) != (sk_B_2))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('31', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k1_tarski @ X0) != (sk_B_2))
% 0.23/0.55          | ((sk_B_2) = (k1_xboole_0))
% 0.23/0.55          | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.23/0.55  thf('32', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) != (sk_B_2))
% 0.23/0.55          | (v1_xboole_0 @ X0)
% 0.23/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.55          | ((sk_A) = (k1_xboole_0))
% 0.23/0.55          | ((sk_B_2) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['22', '31'])).
% 0.23/0.55  thf('33', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((X0) != (sk_B_2))
% 0.23/0.55          | (v1_xboole_0 @ X0)
% 0.23/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.55          | ((sk_B_2) = (k1_xboole_0))
% 0.23/0.55          | ((sk_A) = (k1_xboole_0))
% 0.23/0.55          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.55          | (v1_xboole_0 @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['18', '32'])).
% 0.23/0.55  thf('34', plain,
% 0.23/0.55      ((((sk_A) = (k1_xboole_0))
% 0.23/0.55        | ((sk_B_2) = (k1_xboole_0))
% 0.23/0.55        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.23/0.55        | (v1_xboole_0 @ sk_B_2))),
% 0.23/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.23/0.55  thf('35', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('36', plain,
% 0.23/0.56      ((((sk_A) = (k1_xboole_0))
% 0.23/0.56        | ((sk_B_2) = (k1_xboole_0))
% 0.23/0.56        | (v1_xboole_0 @ sk_B_2))),
% 0.23/0.56      inference('simplify_reflect+', [status(thm)], ['34', '35'])).
% 0.23/0.56  thf('37', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('38', plain, ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.56      inference('clc', [status(thm)], ['36', '37'])).
% 0.23/0.56  thf('39', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('40', plain,
% 0.23/0.56      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.23/0.56  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.56      inference('simplify_reflect-', [status(thm)], ['11', '16'])).
% 0.23/0.56  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.23/0.56  thf('43', plain, ((v1_xboole_0 @ sk_A)),
% 0.23/0.56      inference('demod', [status(thm)], ['17', '42'])).
% 0.23/0.56  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.23/0.56  
% 0.23/0.56  % SZS output end Refutation
% 0.23/0.56  
% 0.23/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
