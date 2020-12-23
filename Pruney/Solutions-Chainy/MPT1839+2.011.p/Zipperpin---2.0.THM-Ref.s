%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mwubMoqOul

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  406 ( 606 expanded)
%              Number of equality atoms :   43 (  54 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( X16
        = ( k6_domain_1 @ X16 @ ( sk_B @ X16 ) ) )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = X8 )
      | ( ( k1_tarski @ X9 )
       != ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
       != X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mwubMoqOul
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:20:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 114 iterations in 0.067s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(t2_tex_2, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.22/0.53           ( r1_tarski @ A @ B ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.22/0.53              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.22/0.53  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d1_tex_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.53       ( ( v1_zfmisc_1 @ A ) <=>
% 0.22/0.53         ( ?[B:$i]:
% 0.22/0.53           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X16 : $i]:
% 0.22/0.53         (~ (v1_zfmisc_1 @ X16)
% 0.22/0.53          | ((X16) = (k6_domain_1 @ X16 @ (sk_B @ X16)))
% 0.22/0.53          | (v1_xboole_0 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X16 : $i]:
% 0.22/0.53         (~ (v1_zfmisc_1 @ X16)
% 0.22/0.53          | (m1_subset_1 @ (sk_B @ X16) @ X16)
% 0.22/0.53          | (v1_xboole_0 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X14 : $i, X15 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X14)
% 0.22/0.53          | ~ (m1_subset_1 @ X15 @ X14)
% 0.22/0.53          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ X0)
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.53          | (v1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | (v1_xboole_0 @ X0))),
% 0.22/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['1', '5'])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.53  thf(t17_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.22/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.53  thf(t12_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i]:
% 0.22/0.53         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf(t44_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.53          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.53          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.53         (((X7) = (k1_xboole_0))
% 0.22/0.53          | ((X8) = (k1_xboole_0))
% 0.22/0.53          | ((X7) = (X8))
% 0.22/0.53          | ((k1_tarski @ X9) != (k2_xboole_0 @ X7 @ X8)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((k1_tarski @ X2) != (X0))
% 0.22/0.53          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_xboole_0))
% 0.22/0.53          | ((k1_tarski @ X2) = (k1_xboole_0))
% 0.22/0.53          | ((k3_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.53  thf(t1_boole, axiom,
% 0.22/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.53  thf('15', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.53  thf(t49_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i]:
% 0.22/0.53         ((k2_xboole_0 @ (k1_tarski @ X10) @ X11) != (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.53  thf('17', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_xboole_0))
% 0.22/0.53          | ((k3_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2)))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['14', '17'])).
% 0.22/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.22/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.22/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.53          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['18', '21'])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['8', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_tarski @ X0 @ X1)
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['7', '23'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | (r1_tarski @ X0 @ X1))),
% 0.22/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.53          | (r1_tarski @ X0 @ X1)
% 0.22/0.53          | (v1_xboole_0 @ X0)
% 0.22/0.53          | ~ (v1_zfmisc_1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.53  thf('28', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('30', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.53        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.53        | (v1_xboole_0 @ sk_A)
% 0.22/0.53        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['27', '30'])).
% 0.22/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.53  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.53  thf('33', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('34', plain, (((v1_xboole_0 @ sk_A) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.53  thf('35', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('36', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.22/0.53      inference('clc', [status(thm)], ['34', '35'])).
% 0.22/0.53  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
