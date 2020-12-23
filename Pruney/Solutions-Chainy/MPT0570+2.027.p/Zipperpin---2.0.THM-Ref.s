%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S2B2ZCZnnc

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:11 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 111 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  366 ( 860 expanded)
%              Number of equality atoms :   34 (  85 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X18 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('8',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_2 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ ( k2_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ ( k2_relat_1 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_B_2 ) @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( ( k10_relat_1 @ sk_B_2 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ X29 @ X30 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['28'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B_2 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('36',plain,(
    $false ),
    inference('sup-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S2B2ZCZnnc
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:38:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 269 iterations in 0.102s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.36/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(d4_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.36/0.54       ( ![D:$i]:
% 0.36/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.36/0.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.36/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.36/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.36/0.54  thf(t4_boole, axiom,
% 0.36/0.54    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t4_boole])).
% 0.36/0.54  thf(t64_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.36/0.54       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.54         (((X16) != (X18))
% 0.36/0.54          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 0.36/0.54      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X17 : $i, X18 : $i]:
% 0.36/0.54         ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.54  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.36/0.54          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '4'])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.36/0.54          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '4'])).
% 0.36/0.54  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.36/0.54          | ((X1) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['5', '8'])).
% 0.36/0.54  thf(t174_relat_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.36/0.54            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( v1_relat_1 @ B ) =>
% 0.36/0.54          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.36/0.54               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.36/0.54  thf('10', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B_2))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t28_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X11 : $i, X12 : $i]:
% 0.36/0.54         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.54  thf('12', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_2)) = (sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X4 @ X3)
% 0.36/0.54          | (r2_hidden @ X4 @ X2)
% 0.36/0.54          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.36/0.54         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_2)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['12', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((sk_A) = (k1_xboole_0))
% 0.36/0.54          | (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ 
% 0.36/0.54             (k2_relat_1 @ sk_B_2)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['9', '15'])).
% 0.36/0.54  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ (k2_relat_1 @ sk_B_2))),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.36/0.54          | ((X1) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['5', '8'])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ X2)
% 0.36/0.54          | (r2_hidden @ X0 @ X3)
% 0.36/0.54          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ X2)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.36/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (((X0) = (k1_xboole_0))
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X2)
% 0.36/0.54          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ 
% 0.36/0.54             (k3_xboole_0 @ X2 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '21'])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ 
% 0.36/0.54           (k3_xboole_0 @ (k2_relat_1 @ sk_B_2) @ sk_A))
% 0.36/0.54          | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '22'])).
% 0.36/0.54  thf('24', plain, (((k10_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t173_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.54         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X29 : $i, X30 : $i]:
% 0.36/0.54         (((k10_relat_1 @ X29 @ X30) != (k1_xboole_0))
% 0.36/0.54          | (r1_xboole_0 @ (k2_relat_1 @ X29) @ X30)
% 0.36/0.54          | ~ (v1_relat_1 @ X29))),
% 0.36/0.54      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_B_2)
% 0.36/0.54        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_2) @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('27', plain, ((v1_relat_1 @ sk_B_2)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.54        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_2) @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B_2) @ sk_A)),
% 0.36/0.54      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.54  thf(d7_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i]:
% 0.36/0.54         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.36/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (((k3_xboole_0 @ (k2_relat_1 @ sk_B_2) @ sk_A) = (k1_xboole_0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.36/0.54          | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['23', '31'])).
% 0.36/0.54  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      (![X0 : $i]: (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.36/0.54  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.36/0.54  thf('36', plain, ($false), inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
