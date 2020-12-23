%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zrx4RCoWz8

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:56 EST 2020

% Result     : Theorem 4.46s
% Output     : Refutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   68 (  90 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  432 ( 699 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k3_relat_1 @ X30 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X30: $i] :
      ( ( ( k3_relat_1 @ X30 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ X32 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( r1_tarski @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X30: $i] :
      ( ( ( k3_relat_1 @ X30 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( r1_tarski @ ( k1_relat_1 @ X32 ) @ ( k1_relat_1 @ X31 ) )
      | ~ ( r1_tarski @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','31'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ( r1_tarski @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zrx4RCoWz8
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.46/4.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.46/4.64  % Solved by: fo/fo7.sh
% 4.46/4.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.46/4.64  % done 4640 iterations in 4.179s
% 4.46/4.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.46/4.64  % SZS output start Refutation
% 4.46/4.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.46/4.64  thf(sk_B_type, type, sk_B: $i).
% 4.46/4.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.46/4.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.46/4.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.46/4.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.46/4.64  thf(sk_A_type, type, sk_A: $i).
% 4.46/4.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.46/4.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.46/4.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.46/4.64  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 4.46/4.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.46/4.64  thf(t31_relat_1, conjecture,
% 4.46/4.64    (![A:$i]:
% 4.46/4.64     ( ( v1_relat_1 @ A ) =>
% 4.46/4.64       ( ![B:$i]:
% 4.46/4.64         ( ( v1_relat_1 @ B ) =>
% 4.46/4.64           ( ( r1_tarski @ A @ B ) =>
% 4.46/4.64             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 4.46/4.64  thf(zf_stmt_0, negated_conjecture,
% 4.46/4.64    (~( ![A:$i]:
% 4.46/4.64        ( ( v1_relat_1 @ A ) =>
% 4.46/4.64          ( ![B:$i]:
% 4.46/4.64            ( ( v1_relat_1 @ B ) =>
% 4.46/4.64              ( ( r1_tarski @ A @ B ) =>
% 4.46/4.64                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 4.46/4.64    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 4.46/4.64  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf(d6_relat_1, axiom,
% 4.46/4.64    (![A:$i]:
% 4.46/4.64     ( ( v1_relat_1 @ A ) =>
% 4.46/4.64       ( ( k3_relat_1 @ A ) =
% 4.46/4.64         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 4.46/4.64  thf('1', plain,
% 4.46/4.64      (![X30 : $i]:
% 4.46/4.64         (((k3_relat_1 @ X30)
% 4.46/4.64            = (k2_xboole_0 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30)))
% 4.46/4.64          | ~ (v1_relat_1 @ X30))),
% 4.46/4.64      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.46/4.64  thf('2', plain,
% 4.46/4.64      (![X30 : $i]:
% 4.46/4.64         (((k3_relat_1 @ X30)
% 4.46/4.64            = (k2_xboole_0 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30)))
% 4.46/4.64          | ~ (v1_relat_1 @ X30))),
% 4.46/4.64      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.46/4.64  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf(t25_relat_1, axiom,
% 4.46/4.64    (![A:$i]:
% 4.46/4.64     ( ( v1_relat_1 @ A ) =>
% 4.46/4.64       ( ![B:$i]:
% 4.46/4.64         ( ( v1_relat_1 @ B ) =>
% 4.46/4.64           ( ( r1_tarski @ A @ B ) =>
% 4.46/4.64             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 4.46/4.64               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 4.46/4.64  thf('4', plain,
% 4.46/4.64      (![X31 : $i, X32 : $i]:
% 4.46/4.64         (~ (v1_relat_1 @ X31)
% 4.46/4.64          | (r1_tarski @ (k2_relat_1 @ X32) @ (k2_relat_1 @ X31))
% 4.46/4.64          | ~ (r1_tarski @ X32 @ X31)
% 4.46/4.64          | ~ (v1_relat_1 @ X32))),
% 4.46/4.64      inference('cnf', [status(esa)], [t25_relat_1])).
% 4.46/4.64  thf('5', plain,
% 4.46/4.64      ((~ (v1_relat_1 @ sk_A)
% 4.46/4.64        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 4.46/4.64        | ~ (v1_relat_1 @ sk_B))),
% 4.46/4.64      inference('sup-', [status(thm)], ['3', '4'])).
% 4.46/4.64  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 4.46/4.64      inference('demod', [status(thm)], ['5', '6', '7'])).
% 4.46/4.64  thf(t10_xboole_1, axiom,
% 4.46/4.64    (![A:$i,B:$i,C:$i]:
% 4.46/4.64     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 4.46/4.64  thf('9', plain,
% 4.46/4.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.46/4.64         (~ (r1_tarski @ X10 @ X11)
% 4.46/4.64          | (r1_tarski @ X10 @ (k2_xboole_0 @ X12 @ X11)))),
% 4.46/4.64      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.46/4.64  thf('10', plain,
% 4.46/4.64      (![X0 : $i]:
% 4.46/4.64         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 4.46/4.64          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 4.46/4.64      inference('sup-', [status(thm)], ['8', '9'])).
% 4.46/4.64  thf('11', plain,
% 4.46/4.64      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 4.46/4.64        | ~ (v1_relat_1 @ sk_B))),
% 4.46/4.64      inference('sup+', [status(thm)], ['2', '10'])).
% 4.46/4.64  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.46/4.64      inference('demod', [status(thm)], ['11', '12'])).
% 4.46/4.64  thf('14', plain,
% 4.46/4.64      (![X30 : $i]:
% 4.46/4.64         (((k3_relat_1 @ X30)
% 4.46/4.64            = (k2_xboole_0 @ (k1_relat_1 @ X30) @ (k2_relat_1 @ X30)))
% 4.46/4.64          | ~ (v1_relat_1 @ X30))),
% 4.46/4.64      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.46/4.64  thf(d3_tarski, axiom,
% 4.46/4.64    (![A:$i,B:$i]:
% 4.46/4.64     ( ( r1_tarski @ A @ B ) <=>
% 4.46/4.64       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.46/4.64  thf('15', plain,
% 4.46/4.64      (![X1 : $i, X3 : $i]:
% 4.46/4.64         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.46/4.64      inference('cnf', [status(esa)], [d3_tarski])).
% 4.46/4.64  thf('16', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf('17', plain,
% 4.46/4.64      (![X31 : $i, X32 : $i]:
% 4.46/4.64         (~ (v1_relat_1 @ X31)
% 4.46/4.64          | (r1_tarski @ (k1_relat_1 @ X32) @ (k1_relat_1 @ X31))
% 4.46/4.64          | ~ (r1_tarski @ X32 @ X31)
% 4.46/4.64          | ~ (v1_relat_1 @ X32))),
% 4.46/4.64      inference('cnf', [status(esa)], [t25_relat_1])).
% 4.46/4.64  thf('18', plain,
% 4.46/4.64      ((~ (v1_relat_1 @ sk_A)
% 4.46/4.64        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.46/4.64        | ~ (v1_relat_1 @ sk_B))),
% 4.46/4.64      inference('sup-', [status(thm)], ['16', '17'])).
% 4.46/4.64  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 4.46/4.64      inference('demod', [status(thm)], ['18', '19', '20'])).
% 4.46/4.64  thf(t28_xboole_1, axiom,
% 4.46/4.64    (![A:$i,B:$i]:
% 4.46/4.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.46/4.64  thf('22', plain,
% 4.46/4.64      (![X13 : $i, X14 : $i]:
% 4.46/4.64         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 4.46/4.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.46/4.64  thf('23', plain,
% 4.46/4.64      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.46/4.64         = (k1_relat_1 @ sk_A))),
% 4.46/4.64      inference('sup-', [status(thm)], ['21', '22'])).
% 4.46/4.64  thf(t48_xboole_1, axiom,
% 4.46/4.64    (![A:$i,B:$i]:
% 4.46/4.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.46/4.64  thf('24', plain,
% 4.46/4.64      (![X18 : $i, X19 : $i]:
% 4.46/4.64         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 4.46/4.64           = (k3_xboole_0 @ X18 @ X19))),
% 4.46/4.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.46/4.64  thf(d5_xboole_0, axiom,
% 4.46/4.64    (![A:$i,B:$i,C:$i]:
% 4.46/4.64     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.46/4.64       ( ![D:$i]:
% 4.46/4.64         ( ( r2_hidden @ D @ C ) <=>
% 4.46/4.64           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.46/4.64  thf('25', plain,
% 4.46/4.64      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 4.46/4.64         (~ (r2_hidden @ X8 @ X7)
% 4.46/4.64          | ~ (r2_hidden @ X8 @ X6)
% 4.46/4.64          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 4.46/4.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.46/4.64  thf('26', plain,
% 4.46/4.64      (![X5 : $i, X6 : $i, X8 : $i]:
% 4.46/4.64         (~ (r2_hidden @ X8 @ X6)
% 4.46/4.64          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 4.46/4.64      inference('simplify', [status(thm)], ['25'])).
% 4.46/4.64  thf('27', plain,
% 4.46/4.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.46/4.64         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.46/4.64          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.46/4.64      inference('sup-', [status(thm)], ['24', '26'])).
% 4.46/4.64  thf('28', plain,
% 4.46/4.64      (![X0 : $i]:
% 4.46/4.64         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_A))
% 4.46/4.64          | ~ (r2_hidden @ X0 @ 
% 4.46/4.64               (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 4.46/4.64      inference('sup-', [status(thm)], ['23', '27'])).
% 4.46/4.64  thf('29', plain,
% 4.46/4.64      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 4.46/4.64         (~ (r2_hidden @ X8 @ X7)
% 4.46/4.64          | (r2_hidden @ X8 @ X5)
% 4.46/4.64          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 4.46/4.64      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.46/4.64  thf('30', plain,
% 4.46/4.64      (![X5 : $i, X6 : $i, X8 : $i]:
% 4.46/4.64         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 4.46/4.64      inference('simplify', [status(thm)], ['29'])).
% 4.46/4.64  thf('31', plain,
% 4.46/4.64      (![X0 : $i]:
% 4.46/4.64         ~ (r2_hidden @ X0 @ 
% 4.46/4.64            (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 4.46/4.64      inference('clc', [status(thm)], ['28', '30'])).
% 4.46/4.64  thf('32', plain,
% 4.46/4.64      (![X0 : $i]:
% 4.46/4.64         (r1_tarski @ 
% 4.46/4.64          (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)) @ X0)),
% 4.46/4.64      inference('sup-', [status(thm)], ['15', '31'])).
% 4.46/4.64  thf(t44_xboole_1, axiom,
% 4.46/4.64    (![A:$i,B:$i,C:$i]:
% 4.46/4.64     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 4.46/4.64       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.46/4.64  thf('33', plain,
% 4.46/4.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.46/4.64         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 4.46/4.64          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 4.46/4.64      inference('cnf', [status(esa)], [t44_xboole_1])).
% 4.46/4.64  thf('34', plain,
% 4.46/4.64      (![X0 : $i]:
% 4.46/4.64         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 4.46/4.64          (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 4.46/4.64      inference('sup-', [status(thm)], ['32', '33'])).
% 4.46/4.64  thf('35', plain,
% 4.46/4.64      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 4.46/4.64        | ~ (v1_relat_1 @ sk_B))),
% 4.46/4.64      inference('sup+', [status(thm)], ['14', '34'])).
% 4.46/4.64  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf('37', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.46/4.64      inference('demod', [status(thm)], ['35', '36'])).
% 4.46/4.64  thf(t8_xboole_1, axiom,
% 4.46/4.64    (![A:$i,B:$i,C:$i]:
% 4.46/4.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 4.46/4.64       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.46/4.64  thf('38', plain,
% 4.46/4.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.46/4.64         (~ (r1_tarski @ X20 @ X21)
% 4.46/4.64          | ~ (r1_tarski @ X22 @ X21)
% 4.46/4.64          | (r1_tarski @ (k2_xboole_0 @ X20 @ X22) @ X21))),
% 4.46/4.64      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.46/4.64  thf('39', plain,
% 4.46/4.64      (![X0 : $i]:
% 4.46/4.64         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 4.46/4.64           (k3_relat_1 @ sk_B))
% 4.46/4.64          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 4.46/4.64      inference('sup-', [status(thm)], ['37', '38'])).
% 4.46/4.64  thf('40', plain,
% 4.46/4.64      ((r1_tarski @ 
% 4.46/4.64        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 4.46/4.64        (k3_relat_1 @ sk_B))),
% 4.46/4.64      inference('sup-', [status(thm)], ['13', '39'])).
% 4.46/4.64  thf('41', plain,
% 4.46/4.64      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 4.46/4.64        | ~ (v1_relat_1 @ sk_A))),
% 4.46/4.64      inference('sup+', [status(thm)], ['1', '40'])).
% 4.46/4.64  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 4.46/4.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.46/4.64  thf('43', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.46/4.64      inference('demod', [status(thm)], ['41', '42'])).
% 4.46/4.64  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 4.46/4.64  
% 4.46/4.64  % SZS output end Refutation
% 4.46/4.64  
% 4.46/4.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
