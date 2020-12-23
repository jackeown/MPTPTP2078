%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A7gRYrBJBB

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 436 expanded)
%              Number of leaves         :   20 ( 134 expanded)
%              Depth                    :   18
%              Number of atoms          :  473 (4204 expanded)
%              Number of equality atoms :   18 ( 238 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t32_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ~ ( ( r1_tarski @ A @ B )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ~ ( ( r2_hidden @ C @ A )
                  & ! [D: $i] :
                      ( ( v3_ordinal1 @ D )
                     => ( ( r2_hidden @ D @ A )
                       => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v3_ordinal1 @ B )
       => ~ ( ( r1_tarski @ A @ B )
            & ( A != k1_xboole_0 )
            & ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ~ ( ( r2_hidden @ C @ A )
                    & ! [D: $i] :
                        ( ( v3_ordinal1 @ D )
                       => ( ( r2_hidden @ D @ A )
                         => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_ordinal1])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('24',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X20: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X20 ) @ sk_A )
      | ~ ( r2_hidden @ X20 @ sk_A )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('29',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('31',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( r1_ordinal1 @ X17 @ X16 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( sk_C_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,
    ( ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('43',plain,(
    ! [X20: $i] :
      ( ( v3_ordinal1 @ ( sk_D_1 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('46',plain,(
    v3_ordinal1 @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D_1 @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X20: $i] :
      ( ~ ( r1_ordinal1 @ X20 @ ( sk_D_1 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('51',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A7gRYrBJBB
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 292 iterations in 0.109s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.56  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.56  thf('0', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.56  thf(t2_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.56       ( ( A ) = ( B ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i]:
% 0.21/0.56         (((X7) = (X6))
% 0.21/0.56          | (r2_hidden @ (sk_C @ X6 @ X7) @ X6)
% 0.21/0.56          | (r2_hidden @ (sk_C @ X6 @ X7) @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_tarski])).
% 0.21/0.56  thf(t7_ordinal1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.21/0.56          | ((X1) = (X0))
% 0.21/0.56          | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.56  thf(t32_ordinal1, conjecture,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56            ( ![C:$i]:
% 0.21/0.56              ( ( v3_ordinal1 @ C ) =>
% 0.21/0.56                ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.56                     ( ![D:$i]:
% 0.21/0.56                       ( ( v3_ordinal1 @ D ) =>
% 0.21/0.56                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i]:
% 0.21/0.56        ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56               ( ![C:$i]:
% 0.21/0.56                 ( ( v3_ordinal1 @ C ) =>
% 0.21/0.56                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.56                        ( ![D:$i]:
% 0.21/0.56                          ( ( v3_ordinal1 @ D ) =>
% 0.21/0.56                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.21/0.56  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t28_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i]:
% 0.21/0.56         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.56  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf(d4_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.56          | (r2_hidden @ X4 @ X2)
% 0.21/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.56         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      ((((sk_A) = (k1_xboole_0))
% 0.21/0.56        | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '10'])).
% 0.21/0.56  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('13', plain, ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B)),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ X2)
% 0.21/0.56          | (r2_hidden @ X0 @ X3)
% 0.21/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ X2)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 0.21/0.56          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.21/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '17'])).
% 0.21/0.56  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.56         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.56  thf('22', plain, ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf(t7_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ~( ( r2_hidden @ A @ B ) & 
% 0.21/0.56          ( ![C:$i]:
% 0.21/0.56            ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.56                 ( ![D:$i]:
% 0.21/0.56                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X11 @ X12) | (r2_hidden @ (sk_C_1 @ X12) @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.56  thf('24', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X20 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_D_1 @ X20) @ sk_A)
% 0.21/0.56          | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.56          | ~ (v3_ordinal1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.21/0.56        | (r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('27', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.56  thf('29', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf(t23_ordinal1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i]:
% 0.21/0.56         ((v3_ordinal1 @ X14)
% 0.21/0.56          | ~ (v3_ordinal1 @ X15)
% 0.21/0.56          | ~ (r2_hidden @ X14 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((~ (v3_ordinal1 @ sk_B) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('33', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain, ((r2_hidden @ (sk_D_1 @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['26', '33'])).
% 0.21/0.56  thf('35', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf(t26_ordinal1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.56           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ X16)
% 0.21/0.56          | (r1_ordinal1 @ X17 @ X16)
% 0.21/0.56          | (r2_hidden @ X16 @ X17)
% 0.21/0.56          | ~ (v3_ordinal1 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X11 @ X12)
% 0.21/0.56          | ~ (r2_hidden @ X13 @ X12)
% 0.21/0.56          | ~ (r2_hidden @ X13 @ (sk_C_1 @ X12)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.56      inference('condensation', [status(thm)], ['37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v3_ordinal1 @ (sk_C_1 @ X0))
% 0.21/0.56          | (r1_ordinal1 @ (sk_C_1 @ X0) @ X1)
% 0.21/0.56          | ~ (v3_ordinal1 @ X1)
% 0.21/0.56          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.56          | ~ (v3_ordinal1 @ X0)
% 0.21/0.56          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['35', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D_1 @ (sk_C_1 @ sk_A)))
% 0.21/0.56        | ~ (v3_ordinal1 @ (sk_D_1 @ (sk_C_1 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['34', '40'])).
% 0.21/0.56  thf('42', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X20 : $i]:
% 0.21/0.56         ((v3_ordinal1 @ (sk_D_1 @ X20))
% 0.21/0.56          | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.56          | ~ (v3_ordinal1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.21/0.56        | (v3_ordinal1 @ (sk_D_1 @ (sk_C_1 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.56  thf('45', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('46', plain, ((v3_ordinal1 @ (sk_D_1 @ (sk_C_1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      ((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D_1 @ (sk_C_1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (![X20 : $i]:
% 0.21/0.56         (~ (r1_ordinal1 @ X20 @ (sk_D_1 @ X20))
% 0.21/0.56          | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.56          | ~ (v3_ordinal1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.21/0.56        | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.56  thf('50', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('51', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.56  thf('52', plain, ($false),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
