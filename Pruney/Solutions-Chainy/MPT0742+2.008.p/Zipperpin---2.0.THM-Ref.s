%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.33hBg9LFMS

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 328 expanded)
%              Number of leaves         :   16 ( 101 expanded)
%              Depth                    :   17
%              Number of atoms          :  366 (3346 expanded)
%              Number of equality atoms :    9 ( 148 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ ( sk_D @ X12 ) @ sk_A )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('13',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_ordinal1 @ ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['4','15'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C_1 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('18',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ ( sk_D @ X12 ) @ sk_A )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('23',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('25',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ( r1_ordinal1 @ X11 @ X10 )
      | ( r2_hidden @ X10 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( sk_C_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,
    ( ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('37',plain,(
    ! [X12: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X12 ) )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,(
    v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ~ ( r1_ordinal1 @ X12 @ ( sk_D @ X12 ) )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('45',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.33hBg9LFMS
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 143 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.50  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.50  thf(t7_xboole_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.50  thf(t32_ordinal1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50            ( ![C:$i]:
% 0.21/0.50              ( ( v3_ordinal1 @ C ) =>
% 0.21/0.50                ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.50                     ( ![D:$i]:
% 0.21/0.50                       ( ( v3_ordinal1 @ D ) =>
% 0.21/0.50                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50               ( ![C:$i]:
% 0.21/0.50                 ( ( v3_ordinal1 @ C ) =>
% 0.21/0.50                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.50                        ( ![D:$i]:
% 0.21/0.50                          ( ( v3_ordinal1 @ D ) =>
% 0.21/0.50                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X12 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X12) @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ X12 @ sk_A)
% 0.21/0.50          | ~ (v3_ordinal1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.21/0.50        | (r2_hidden @ (sk_D @ (sk_B @ sk_A)) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.21/0.50        | (r2_hidden @ (sk_D @ (sk_B @ sk_A)) @ sk_A))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.50  thf('6', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.50  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_1)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(t23_ordinal1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ X8) | ~ (v3_ordinal1 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((~ (v3_ordinal1 @ sk_B_1) | (v3_ordinal1 @ (sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain, ((v3_ordinal1 @ (sk_B @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain, ((r2_hidden @ (sk_D @ (sk_B @ sk_A)) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '15'])).
% 0.21/0.50  thf(t7_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ~( ( r2_hidden @ A @ B ) & 
% 0.21/0.50          ( ![C:$i]:
% 0.21/0.50            ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.50                 ( ![D:$i]:
% 0.21/0.50                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X5 @ X6) | (r2_hidden @ (sk_C_1 @ X6) @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.50  thf('18', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X12 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X12) @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ X12 @ sk_A)
% 0.21/0.50          | ~ (v3_ordinal1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.21/0.50        | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('23', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ X8) | ~ (v3_ordinal1 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((~ (v3_ordinal1 @ sk_B_1) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain, ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '27'])).
% 0.21/0.50  thf('29', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf(t26_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X10)
% 0.21/0.50          | (r1_ordinal1 @ X11 @ X10)
% 0.21/0.50          | (r2_hidden @ X10 @ X11)
% 0.21/0.50          | ~ (v3_ordinal1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.50          | ~ (r2_hidden @ X7 @ X6)
% 0.21/0.50          | ~ (r2_hidden @ X7 @ (sk_C_1 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.50      inference('condensation', [status(thm)], ['31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ (sk_C_1 @ X0))
% 0.21/0.50          | (r1_ordinal1 @ (sk_C_1 @ X0) @ X1)
% 0.21/0.50          | ~ (v3_ordinal1 @ X1)
% 0.21/0.50          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50          | ~ (v3_ordinal1 @ X0)
% 0.21/0.50          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))
% 0.21/0.50        | ~ (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '34'])).
% 0.21/0.50  thf('36', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X12 : $i]:
% 0.21/0.50         ((v3_ordinal1 @ (sk_D @ X12))
% 0.21/0.50          | ~ (r2_hidden @ X12 @ sk_A)
% 0.21/0.50          | ~ (v3_ordinal1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.21/0.50        | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('40', plain, ((v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      ((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X12 : $i]:
% 0.21/0.50         (~ (r1_ordinal1 @ X12 @ (sk_D @ X12))
% 0.21/0.50          | ~ (r2_hidden @ X12 @ sk_A)
% 0.21/0.50          | ~ (v3_ordinal1 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.21/0.50        | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('45', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('46', plain, ($false),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
