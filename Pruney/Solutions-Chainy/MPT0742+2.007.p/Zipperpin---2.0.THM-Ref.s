%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1DBlEUUe1N

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:51 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 226 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  519 (2131 expanded)
%              Number of equality atoms :   24 (  99 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X16: $i] :
      ( ( r2_hidden @ ( sk_D @ X16 ) @ sk_A )
      | ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_xboole_0 = sk_A )
    | ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_2 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_2 @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('19',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_ordinal1 @ ( sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_2 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['10','21'])).

thf('23',plain,(
    v3_ordinal1 @ ( sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( r2_hidden @ X9 @ ( sk_C_2 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_2 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_2 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( r1_ordinal1 @ ( sk_C_2 @ sk_A ) @ ( sk_D @ ( sk_C_2 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X16 ) )
      | ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_xboole_0 = sk_A )
    | ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_ordinal1 @ ( sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('36',plain,(
    v3_ordinal1 @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_ordinal1 @ ( sk_C_2 @ sk_A ) @ ( sk_D @ ( sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X16: $i] :
      ( ~ ( r1_ordinal1 @ X16 @ ( sk_D @ X16 ) )
      | ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_2 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ ( sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('41',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X16: $i] :
      ( ( r2_hidden @ ( sk_D @ X16 ) @ sk_A )
      | ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('54',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( v3_ordinal1 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_ordinal1 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('61',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1DBlEUUe1N
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 275 iterations in 0.090s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i > $i).
% 0.35/0.54  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.35/0.54  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.54  thf('0', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.54  thf(t2_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.35/0.54       ( ( A ) = ( B ) ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i]:
% 0.35/0.54         (((X5) = (X4))
% 0.35/0.54          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.35/0.54          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_tarski])).
% 0.35/0.54  thf(t7_ordinal1, axiom,
% 0.35/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X14 : $i, X15 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.35/0.54          | ((X0) = (X1))
% 0.35/0.54          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k1_xboole_0) = (X0))
% 0.35/0.54          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['0', '3'])).
% 0.35/0.54  thf(t7_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ~( ( r2_hidden @ A @ B ) & 
% 0.35/0.54          ( ![C:$i]:
% 0.35/0.54            ( ~( ( r2_hidden @ C @ B ) & 
% 0.35/0.54                 ( ![D:$i]:
% 0.35/0.54                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C_2 @ X8) @ X8))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.54  thf(t32_ordinal1, conjecture,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v3_ordinal1 @ B ) =>
% 0.35/0.54       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54            ( ![C:$i]:
% 0.35/0.54              ( ( v3_ordinal1 @ C ) =>
% 0.35/0.54                ( ~( ( r2_hidden @ C @ A ) & 
% 0.35/0.54                     ( ![D:$i]:
% 0.35/0.54                       ( ( v3_ordinal1 @ D ) =>
% 0.35/0.54                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i]:
% 0.35/0.54        ( ( v3_ordinal1 @ B ) =>
% 0.35/0.54          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54               ( ![C:$i]:
% 0.35/0.54                 ( ( v3_ordinal1 @ C ) =>
% 0.35/0.54                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.35/0.54                        ( ![D:$i]:
% 0.35/0.54                          ( ( v3_ordinal1 @ D ) =>
% 0.35/0.54                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X16 : $i]:
% 0.35/0.54         ((r2_hidden @ (sk_D @ X16) @ sk_A)
% 0.35/0.54          | ~ (r2_hidden @ X16 @ sk_A)
% 0.35/0.54          | ~ (v3_ordinal1 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((((k1_xboole_0) = (sk_A))
% 0.35/0.54        | ~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.35/0.54        | (r2_hidden @ (sk_D @ (sk_C_2 @ sk_A)) @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      ((~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.35/0.54        | (r2_hidden @ (sk_D @ (sk_C_2 @ sk_A)) @ sk_A))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.54  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(d3_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.54          | (r2_hidden @ X0 @ X2)
% 0.35/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      ((((k1_xboole_0) = (sk_A)) | (r2_hidden @ (sk_C_2 @ sk_A) @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '14'])).
% 0.35/0.54  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('17', plain, ((r2_hidden @ (sk_C_2 @ sk_A) @ sk_B)),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.35/0.54  thf(t23_ordinal1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i]:
% 0.35/0.54         ((v3_ordinal1 @ X10)
% 0.35/0.54          | ~ (v3_ordinal1 @ X11)
% 0.35/0.54          | ~ (r2_hidden @ X10 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      ((~ (v3_ordinal1 @ sk_B) | (v3_ordinal1 @ (sk_C_2 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.54  thf('20', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('21', plain, ((v3_ordinal1 @ (sk_C_2 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf('22', plain, ((r2_hidden @ (sk_D @ (sk_C_2 @ sk_A)) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['10', '21'])).
% 0.35/0.54  thf('23', plain, ((v3_ordinal1 @ (sk_C_2 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf(t26_ordinal1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.35/0.54           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X12 : $i, X13 : $i]:
% 0.35/0.54         (~ (v3_ordinal1 @ X12)
% 0.35/0.54          | (r1_ordinal1 @ X13 @ X12)
% 0.35/0.54          | (r2_hidden @ X12 @ X13)
% 0.35/0.54          | ~ (v3_ordinal1 @ X13))),
% 0.35/0.54      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X7 @ X8)
% 0.35/0.54          | ~ (r2_hidden @ X9 @ X8)
% 0.35/0.54          | ~ (r2_hidden @ X9 @ (sk_C_2 @ X8)))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X1 @ (sk_C_2 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.54      inference('condensation', [status(thm)], ['25'])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (v3_ordinal1 @ (sk_C_2 @ X0))
% 0.35/0.54          | (r1_ordinal1 @ (sk_C_2 @ X0) @ X1)
% 0.35/0.54          | ~ (v3_ordinal1 @ X1)
% 0.35/0.54          | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['24', '26'])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.35/0.54          | ~ (v3_ordinal1 @ X0)
% 0.35/0.54          | (r1_ordinal1 @ (sk_C_2 @ sk_A) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['23', '27'])).
% 0.35/0.54  thf('29', plain,
% 0.35/0.54      (((r1_ordinal1 @ (sk_C_2 @ sk_A) @ (sk_D @ (sk_C_2 @ sk_A)))
% 0.35/0.54        | ~ (v3_ordinal1 @ (sk_D @ (sk_C_2 @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['22', '28'])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.54  thf('31', plain,
% 0.35/0.54      (![X16 : $i]:
% 0.35/0.54         ((v3_ordinal1 @ (sk_D @ X16))
% 0.35/0.54          | ~ (r2_hidden @ X16 @ sk_A)
% 0.35/0.54          | ~ (v3_ordinal1 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      ((((k1_xboole_0) = (sk_A))
% 0.35/0.54        | ~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.35/0.54        | (v3_ordinal1 @ (sk_D @ (sk_C_2 @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.54  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      ((~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.35/0.54        | (v3_ordinal1 @ (sk_D @ (sk_C_2 @ sk_A))))),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf('35', plain, ((v3_ordinal1 @ (sk_C_2 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf('36', plain, ((v3_ordinal1 @ (sk_D @ (sk_C_2 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      ((r1_ordinal1 @ (sk_C_2 @ sk_A) @ (sk_D @ (sk_C_2 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['29', '36'])).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X16 : $i]:
% 0.35/0.54         (~ (r1_ordinal1 @ X16 @ (sk_D @ X16))
% 0.35/0.54          | ~ (r2_hidden @ X16 @ sk_A)
% 0.35/0.54          | ~ (v3_ordinal1 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      ((~ (v3_ordinal1 @ (sk_C_2 @ sk_A))
% 0.35/0.54        | ~ (r2_hidden @ (sk_C_2 @ sk_A) @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('40', plain, ((v3_ordinal1 @ (sk_C_2 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf('41', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.54  thf('42', plain,
% 0.35/0.54      (![X4 : $i, X5 : $i]:
% 0.35/0.54         (((X5) = (X4))
% 0.35/0.54          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.35/0.54          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_tarski])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      (![X14 : $i, X15 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.54  thf('44', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 0.35/0.54          | ((X1) = (X0))
% 0.35/0.54          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ X1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.54  thf('45', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((X0) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['41', '44'])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      (![X16 : $i]:
% 0.35/0.54         ((r2_hidden @ (sk_D @ X16) @ sk_A)
% 0.35/0.54          | ~ (r2_hidden @ X16 @ sk_A)
% 0.35/0.54          | ~ (v3_ordinal1 @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      ((((sk_A) = (k1_xboole_0))
% 0.35/0.54        | ~ (v3_ordinal1 @ (sk_C_1 @ k1_xboole_0 @ sk_A))
% 0.35/0.54        | (r2_hidden @ (sk_D @ (sk_C_1 @ k1_xboole_0 @ sk_A)) @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((X0) = (k1_xboole_0))
% 0.35/0.54          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['41', '44'])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      ((((sk_A) = (k1_xboole_0))
% 0.35/0.54        | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_B))),
% 0.35/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.54  thf('51', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('52', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_B)),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.35/0.54  thf('53', plain,
% 0.35/0.54      (![X10 : $i, X11 : $i]:
% 0.35/0.54         ((v3_ordinal1 @ X10)
% 0.35/0.54          | ~ (v3_ordinal1 @ X11)
% 0.35/0.54          | ~ (r2_hidden @ X10 @ X11))),
% 0.35/0.54      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      ((~ (v3_ordinal1 @ sk_B) | (v3_ordinal1 @ (sk_C_1 @ k1_xboole_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.35/0.54  thf('55', plain, ((v3_ordinal1 @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('56', plain, ((v3_ordinal1 @ (sk_C_1 @ k1_xboole_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      ((((sk_A) = (k1_xboole_0))
% 0.35/0.54        | (r2_hidden @ (sk_D @ (sk_C_1 @ k1_xboole_0 @ sk_A)) @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['47', '56'])).
% 0.35/0.54  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      ((r2_hidden @ (sk_D @ (sk_C_1 @ k1_xboole_0 @ sk_A)) @ sk_A)),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (![X7 : $i, X8 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C_2 @ X8) @ X8))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.35/0.54  thf('61', plain, ((r2_hidden @ (sk_C_2 @ sk_A) @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.35/0.54  thf('62', plain, ($false),
% 0.35/0.54      inference('demod', [status(thm)], ['39', '40', '61'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
