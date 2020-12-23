%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kR26soyE9h

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:26 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   73 (  91 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  432 ( 584 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X53: $i,X54: $i] :
      ( ( v1_xboole_0 @ X53 )
      | ~ ( v1_zfmisc_1 @ X53 )
      | ( X54 = X53 )
      | ~ ( r1_tarski @ X54 @ X53 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X15 ) @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','33'])).

thf('35',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kR26soyE9h
% 0.13/0.37  % Computer   : n007.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 20:20:06 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.90/1.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.09  % Solved by: fo/fo7.sh
% 0.90/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.09  % done 1046 iterations in 0.609s
% 0.90/1.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.09  % SZS output start Refutation
% 0.90/1.09  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.09  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.09  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.90/1.09  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.90/1.09  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.09  thf(t2_tex_2, conjecture,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.90/1.09           ( r1_tarski @ A @ B ) ) ) ))).
% 0.90/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.09    (~( ![A:$i]:
% 0.90/1.09        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.90/1.09          ( ![B:$i]:
% 0.90/1.09            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.90/1.09              ( r1_tarski @ A @ B ) ) ) ) )),
% 0.90/1.09    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 0.90/1.09  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t17_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.09  thf('1', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 0.90/1.09      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.09  thf(t1_tex_2, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.90/1.09           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.90/1.09  thf('2', plain,
% 0.90/1.09      (![X53 : $i, X54 : $i]:
% 0.90/1.09         ((v1_xboole_0 @ X53)
% 0.90/1.09          | ~ (v1_zfmisc_1 @ X53)
% 0.90/1.09          | ((X54) = (X53))
% 0.90/1.09          | ~ (r1_tarski @ X54 @ X53)
% 0.90/1.09          | (v1_xboole_0 @ X54))),
% 0.90/1.09      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.90/1.09  thf('3', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((v1_xboole_0 @ (k3_xboole_0 @ X0 @ X1))
% 0.90/1.09          | ((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.90/1.09          | ~ (v1_zfmisc_1 @ X0)
% 0.90/1.09          | (v1_xboole_0 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.09  thf('4', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('5', plain,
% 0.90/1.09      (((v1_xboole_0 @ sk_A)
% 0.90/1.09        | ~ (v1_zfmisc_1 @ sk_A)
% 0.90/1.09        | ((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.09  thf('6', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('7', plain,
% 0.90/1.09      (((v1_xboole_0 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['5', '6'])).
% 0.90/1.09  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.90/1.09      inference('clc', [status(thm)], ['7', '8'])).
% 0.90/1.09  thf(t100_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.09  thf('10', plain,
% 0.90/1.09      (![X16 : $i, X17 : $i]:
% 0.90/1.09         ((k4_xboole_0 @ X16 @ X17)
% 0.90/1.09           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.09  thf('11', plain,
% 0.90/1.09      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.09  thf(d1_xboole_0, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.90/1.09  thf('12', plain,
% 0.90/1.09      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.90/1.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.09  thf(idempotence_k3_xboole_0, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.90/1.09  thf('13', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 0.90/1.09      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.09  thf('14', plain,
% 0.90/1.09      (![X16 : $i, X17 : $i]:
% 0.90/1.09         ((k4_xboole_0 @ X16 @ X17)
% 0.90/1.09           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.09  thf('15', plain,
% 0.90/1.09      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.09      inference('sup+', [status(thm)], ['13', '14'])).
% 0.90/1.09  thf(t36_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.09  thf('16', plain,
% 0.90/1.09      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.90/1.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.09  thf('17', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.90/1.09      inference('sup+', [status(thm)], ['15', '16'])).
% 0.90/1.09  thf(d3_tarski, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.09       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.09  thf('18', plain,
% 0.90/1.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X3 @ X4)
% 0.90/1.09          | (r2_hidden @ X3 @ X5)
% 0.90/1.09          | ~ (r1_tarski @ X4 @ X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.09  thf('19', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.09  thf('20', plain,
% 0.90/1.09      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.09      inference('sup+', [status(thm)], ['13', '14'])).
% 0.90/1.09  thf(d5_xboole_0, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.90/1.09       ( ![D:$i]:
% 0.90/1.09         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.09           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.90/1.09  thf('21', plain,
% 0.90/1.09      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X11 @ X10)
% 0.90/1.09          | ~ (r2_hidden @ X11 @ X9)
% 0.90/1.09          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.09  thf('22', plain,
% 0.90/1.09      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X11 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['21'])).
% 0.90/1.09  thf('23', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.90/1.09          | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['20', '22'])).
% 0.90/1.09  thf('24', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.09      inference('clc', [status(thm)], ['19', '23'])).
% 0.90/1.09  thf('25', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['12', '24'])).
% 0.90/1.09  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.09  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.09  thf(t2_tarski, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.90/1.09       ( ( A ) = ( B ) ) ))).
% 0.90/1.09  thf('27', plain,
% 0.90/1.09      (![X14 : $i, X15 : $i]:
% 0.90/1.09         (((X15) = (X14))
% 0.90/1.09          | (r2_hidden @ (sk_C_1 @ X14 @ X15) @ X14)
% 0.90/1.09          | (r2_hidden @ (sk_C_1 @ X14 @ X15) @ X15))),
% 0.90/1.09      inference('cnf', [status(esa)], [t2_tarski])).
% 0.90/1.09  thf('28', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.09  thf('29', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 0.90/1.09          | ((X1) = (X0))
% 0.90/1.09          | ~ (v1_xboole_0 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.09  thf('30', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.09  thf('31', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.09  thf('32', plain,
% 0.90/1.09      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['26', '31'])).
% 0.90/1.09  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['25', '32'])).
% 0.90/1.09  thf('34', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.90/1.09      inference('demod', [status(thm)], ['11', '33'])).
% 0.90/1.09  thf('35', plain,
% 0.90/1.09      (![X4 : $i, X6 : $i]:
% 0.90/1.09         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.90/1.09      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.09  thf('36', plain,
% 0.90/1.09      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X7 @ X8)
% 0.90/1.09          | (r2_hidden @ X7 @ X9)
% 0.90/1.09          | (r2_hidden @ X7 @ X10)
% 0.90/1.09          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.09  thf('37', plain,
% 0.90/1.09      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.09         ((r2_hidden @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.90/1.09          | (r2_hidden @ X7 @ X9)
% 0.90/1.09          | ~ (r2_hidden @ X7 @ X8))),
% 0.90/1.09      inference('simplify', [status(thm)], ['36'])).
% 0.90/1.09  thf('38', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         ((r1_tarski @ X0 @ X1)
% 0.90/1.09          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.90/1.09          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['35', '37'])).
% 0.90/1.09  thf('39', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.09  thf('40', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         ((r2_hidden @ (sk_C @ X2 @ X1) @ X0)
% 0.90/1.09          | (r1_tarski @ X1 @ X2)
% 0.90/1.09          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.09  thf('41', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.09          | (r1_tarski @ sk_A @ X0)
% 0.90/1.09          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['34', '40'])).
% 0.90/1.09  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.09  thf('43', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 0.90/1.09      inference('demod', [status(thm)], ['41', '42'])).
% 0.90/1.09  thf('44', plain,
% 0.90/1.09      (![X4 : $i, X6 : $i]:
% 0.90/1.09         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.90/1.09      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.09  thf('45', plain,
% 0.90/1.09      (((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.09  thf('46', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.90/1.09      inference('simplify', [status(thm)], ['45'])).
% 0.90/1.09  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
