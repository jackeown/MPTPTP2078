%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.muGE0t6Ejq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:22 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   62 (  85 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   17
%              Number of atoms          :  364 ( 606 expanded)
%              Number of equality atoms :   55 (  76 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k4_xboole_0 @ X7 @ X9 )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,
    ( ( k1_xboole_0 != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ~ ( v1_zfmisc_1 @ X16 )
      | ( X16
        = ( k6_domain_1 @ X16 @ ( sk_B @ X16 ) ) )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X11 = X12 )
      | ( ( k1_tarski @ X13 )
       != ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( sk_A = sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('27',plain,
    ( ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
      = sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('29',plain,
    ( ( sk_A = sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['32'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.muGE0t6Ejq
% 0.17/0.37  % Computer   : n020.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 16:14:52 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 175 iterations in 0.058s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.54  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.54  thf(t1_tex_2, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.23/0.54           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.23/0.54              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.23/0.54  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('1', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t12_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.23/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.54  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.54  thf(t46_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.23/0.54  thf('4', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i]:
% 0.23/0.54         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (k1_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.23/0.54  thf('5', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.23/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.23/0.54  thf(t83_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X7 : $i, X9 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ X7 @ X9) | ((k4_xboole_0 @ X7 @ X9) != (X7)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      ((((k1_xboole_0) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf(d1_tex_2, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.54       ( ( v1_zfmisc_1 @ A ) <=>
% 0.23/0.54         ( ?[B:$i]:
% 0.23/0.54           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         (~ (v1_zfmisc_1 @ X16)
% 0.23/0.54          | ((X16) = (k6_domain_1 @ X16 @ (sk_B @ X16)))
% 0.23/0.54          | (v1_xboole_0 @ X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         (~ (v1_zfmisc_1 @ X16)
% 0.23/0.54          | (m1_subset_1 @ (sk_B @ X16) @ X16)
% 0.23/0.54          | (v1_xboole_0 @ X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.23/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X14)
% 0.23/0.54          | ~ (m1_subset_1 @ X15 @ X14)
% 0.23/0.54          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.23/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ X0)
% 0.23/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.54          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.23/0.54          | (v1_xboole_0 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.23/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.54          | (v1_xboole_0 @ X0))),
% 0.23/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.23/0.54          | (v1_xboole_0 @ X0)
% 0.23/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.54          | (v1_xboole_0 @ X0)
% 0.23/0.54          | ~ (v1_zfmisc_1 @ X0))),
% 0.23/0.54      inference('sup+', [status(thm)], ['8', '12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (v1_zfmisc_1 @ X0)
% 0.23/0.54          | (v1_xboole_0 @ X0)
% 0.23/0.54          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.23/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.54  thf('15', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.54  thf(t44_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.54          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.23/0.54          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.54         (((X11) = (k1_xboole_0))
% 0.23/0.54          | ((X12) = (k1_xboole_0))
% 0.23/0.54          | ((X11) = (X12))
% 0.23/0.54          | ((k1_tarski @ X13) != (k2_xboole_0 @ X11 @ X12)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k1_tarski @ X0) != (sk_B_1))
% 0.23/0.54          | ((sk_A) = (sk_B_1))
% 0.23/0.54          | ((sk_B_1) = (k1_xboole_0))
% 0.23/0.54          | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain, (((sk_A) != (sk_B_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k1_tarski @ X0) != (sk_B_1))
% 0.23/0.54          | ((sk_B_1) = (k1_xboole_0))
% 0.23/0.54          | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((X0) != (sk_B_1))
% 0.23/0.54          | (v1_xboole_0 @ X0)
% 0.23/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.23/0.54          | ((sk_A) = (k1_xboole_0))
% 0.23/0.54          | ((sk_B_1) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['14', '19'])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      ((((sk_B_1) = (k1_xboole_0))
% 0.23/0.54        | ((sk_A) = (k1_xboole_0))
% 0.23/0.54        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.23/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.23/0.54  thf('22', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      ((((sk_B_1) = (k1_xboole_0))
% 0.23/0.54        | ((sk_A) = (k1_xboole_0))
% 0.23/0.54        | (v1_xboole_0 @ sk_B_1))),
% 0.23/0.54      inference('simplify_reflect+', [status(thm)], ['21', '22'])).
% 0.23/0.54  thf('24', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('25', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.23/0.54      inference('clc', [status(thm)], ['23', '24'])).
% 0.23/0.54  thf('26', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      ((((k2_xboole_0 @ sk_A @ k1_xboole_0) = (sk_B_1))
% 0.23/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup+', [status(thm)], ['25', '26'])).
% 0.23/0.54  thf(t1_boole, axiom,
% 0.23/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.54  thf('28', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.23/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.23/0.54  thf('29', plain, ((((sk_A) = (sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.54  thf('30', plain, (((sk_A) != (sk_B_1))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.23/0.54  thf('32', plain, ((((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.23/0.54      inference('demod', [status(thm)], ['7', '31'])).
% 0.23/0.54  thf('33', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.23/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.23/0.54  thf(t69_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.54       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      (![X5 : $i, X6 : $i]:
% 0.23/0.54         (~ (r1_xboole_0 @ X5 @ X6)
% 0.23/0.54          | ~ (r1_tarski @ X5 @ X6)
% 0.23/0.54          | (v1_xboole_0 @ X5))),
% 0.23/0.54      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.23/0.54  thf('35', plain, (((v1_xboole_0 @ sk_A) | ~ (r1_tarski @ sk_A @ sk_B_1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.54  thf('36', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('37', plain, ((v1_xboole_0 @ sk_A)),
% 0.23/0.54      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.54  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
