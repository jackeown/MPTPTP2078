%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.91qz8R7sXV

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 232 expanded)
%              Number of leaves         :   17 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  412 (2166 expanded)
%              Number of equality atoms :   15 (  87 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

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
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_D @ X15 ) @ sk_A )
      | ~ ( r2_hidden @ X15 @ sk_A )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_xboole_0 = sk_A )
    | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v3_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['10','25'])).

thf('27',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( sk_C_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X15 ) )
      | ~ ( r2_hidden @ X15 @ sk_A )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_xboole_0 = sk_A )
    | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('40',plain,(
    v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( ~ ( r1_ordinal1 @ X15 @ ( sk_D @ X15 ) )
      | ~ ( r2_hidden @ X15 @ sk_A )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('45',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['10','25'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('47',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.91qz8R7sXV
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 120 iterations in 0.112s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i > $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.57  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.22/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.57  thf('0', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf(d3_tarski, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X1 : $i, X3 : $i]:
% 0.22/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.57  thf(t7_tarski, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ~( ( r2_hidden @ A @ B ) & 
% 0.22/0.57          ( ![C:$i]:
% 0.22/0.57            ( ~( ( r2_hidden @ C @ B ) & 
% 0.22/0.57                 ( ![D:$i]:
% 0.22/0.57                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9) @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_tarski])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf(d10_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X4 : $i, X6 : $i]:
% 0.22/0.57         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_C_1 @ X1) @ X1)
% 0.22/0.57          | ~ (r1_tarski @ X0 @ X1)
% 0.22/0.57          | ((X0) = (X1)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.57  thf(t32_ordinal1, conjecture,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( v3_ordinal1 @ B ) =>
% 0.22/0.57       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57            ( ![C:$i]:
% 0.22/0.57              ( ( v3_ordinal1 @ C ) =>
% 0.22/0.57                ( ~( ( r2_hidden @ C @ A ) & 
% 0.22/0.57                     ( ![D:$i]:
% 0.22/0.57                       ( ( v3_ordinal1 @ D ) =>
% 0.22/0.57                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i]:
% 0.22/0.57        ( ( v3_ordinal1 @ B ) =>
% 0.22/0.57          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57               ( ![C:$i]:
% 0.22/0.57                 ( ( v3_ordinal1 @ C ) =>
% 0.22/0.57                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.22/0.57                        ( ![D:$i]:
% 0.22/0.57                          ( ( v3_ordinal1 @ D ) =>
% 0.22/0.57                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X15 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_D @ X15) @ sk_A)
% 0.22/0.57          | ~ (r2_hidden @ X15 @ sk_A)
% 0.22/0.57          | ~ (v3_ordinal1 @ X15))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      ((((k1_xboole_0) = (sk_A))
% 0.22/0.57        | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.22/0.57        | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.22/0.57        | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.22/0.57  thf('11', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf('13', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.57          | (r2_hidden @ X0 @ X2)
% 0.22/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ sk_A) @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['12', '15'])).
% 0.22/0.57  thf(t23_ordinal1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X11 : $i, X12 : $i]:
% 0.22/0.57         ((v3_ordinal1 @ X11)
% 0.22/0.57          | ~ (v3_ordinal1 @ X12)
% 0.22/0.57          | ~ (r2_hidden @ X11 @ X12))),
% 0.22/0.57      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((r1_tarski @ sk_A @ X0)
% 0.22/0.57          | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.57          | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.57  thf('19', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X4 : $i, X6 : $i]:
% 0.22/0.57         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.22/0.57          | ~ (r1_tarski @ X0 @ sk_A)
% 0.22/0.57          | ((X0) = (sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      ((((k1_xboole_0) = (sk_A)) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '22'])).
% 0.22/0.57  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('25', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf('26', plain, ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '25'])).
% 0.22/0.57  thf('27', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf(t26_ordinal1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.57           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (![X13 : $i, X14 : $i]:
% 0.22/0.57         (~ (v3_ordinal1 @ X13)
% 0.22/0.57          | (r1_ordinal1 @ X14 @ X13)
% 0.22/0.57          | (r2_hidden @ X13 @ X14)
% 0.22/0.57          | ~ (v3_ordinal1 @ X14))),
% 0.22/0.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X8 @ X9)
% 0.22/0.57          | ~ (r2_hidden @ X10 @ X9)
% 0.22/0.57          | ~ (r2_hidden @ X10 @ (sk_C_1 @ X9)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_tarski])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.57      inference('condensation', [status(thm)], ['29'])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v3_ordinal1 @ (sk_C_1 @ X0))
% 0.22/0.57          | (r1_ordinal1 @ (sk_C_1 @ X0) @ X1)
% 0.22/0.57          | ~ (v3_ordinal1 @ X1)
% 0.22/0.57          | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['28', '30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.57          | ~ (v3_ordinal1 @ X0)
% 0.22/0.57          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['27', '31'])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))
% 0.22/0.57        | ~ (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['26', '32'])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X15 : $i]:
% 0.22/0.57         ((v3_ordinal1 @ (sk_D @ X15))
% 0.22/0.57          | ~ (r2_hidden @ X15 @ sk_A)
% 0.22/0.57          | ~ (v3_ordinal1 @ X15))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      ((((k1_xboole_0) = (sk_A))
% 0.22/0.57        | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.22/0.57        | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.57  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.22/0.57        | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.22/0.57  thf('39', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf('40', plain, ((v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      ((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['33', '40'])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (![X15 : $i]:
% 0.22/0.57         (~ (r1_ordinal1 @ X15 @ (sk_D @ X15))
% 0.22/0.57          | ~ (r2_hidden @ X15 @ sk_A)
% 0.22/0.57          | ~ (v3_ordinal1 @ X15))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.22/0.57        | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.57  thf('44', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf('45', plain, ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '25'])).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9) @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [t7_tarski])).
% 0.22/0.57  thf('47', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.57  thf('48', plain, ($false),
% 0.22/0.57      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
