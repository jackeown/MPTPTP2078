%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eoG2czQPY2

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:52 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 228 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  445 (2220 expanded)
%              Number of equality atoms :   21 ( 123 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
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
    ! [X16: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X16 ) @ sk_A )
      | ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('16',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_ordinal1 @ ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['4','18'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('21',plain,(
    r2_hidden @ ( sk_C @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X16 ) @ sk_A )
      | ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( sk_C @ sk_A ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('32',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['23','34'])).

thf('36',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( sk_C @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,
    ( ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('44',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( sk_D_1 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D_1 @ ( sk_C @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('49',plain,(
    v3_ordinal1 @ ( sk_D_1 @ ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X16: $i] :
      ( ~ ( r1_ordinal1 @ X16 @ ( sk_D_1 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('54',plain,(
    r2_hidden @ ( sk_C @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eoG2czQPY2
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 181 iterations in 0.161s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.64  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.46/0.64  thf(t7_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf(t32_ordinal1, conjecture,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v3_ordinal1 @ B ) =>
% 0.46/0.64       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64            ( ![C:$i]:
% 0.46/0.64              ( ( v3_ordinal1 @ C ) =>
% 0.46/0.64                ( ~( ( r2_hidden @ C @ A ) & 
% 0.46/0.64                     ( ![D:$i]:
% 0.46/0.64                       ( ( v3_ordinal1 @ D ) =>
% 0.46/0.64                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i]:
% 0.46/0.64        ( ( v3_ordinal1 @ B ) =>
% 0.46/0.64          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.64               ( ![C:$i]:
% 0.46/0.64                 ( ( v3_ordinal1 @ C ) =>
% 0.46/0.64                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.46/0.64                        ( ![D:$i]:
% 0.46/0.64                          ( ( v3_ordinal1 @ D ) =>
% 0.46/0.64                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X16 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_D_1 @ X16) @ sk_A)
% 0.46/0.64          | ~ (r2_hidden @ X16 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))
% 0.46/0.64        | ~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.46/0.64        | (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A)) @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.64  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.46/0.64        | (r2_hidden @ (sk_D_1 @ (sk_B @ sk_A)) @ sk_A))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('6', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t28_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X7 : $i, X8 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('8', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf(d4_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.64           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.64          | (r2_hidden @ X4 @ X2)
% 0.46/0.64          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.64         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '11'])).
% 0.46/0.64  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('14', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_1)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf(t23_ordinal1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((v3_ordinal1 @ X12)
% 0.46/0.64          | ~ (v3_ordinal1 @ X13)
% 0.46/0.64          | ~ (r2_hidden @ X12 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ sk_B_1) | (v3_ordinal1 @ (sk_B @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('17', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('18', plain, ((v3_ordinal1 @ (sk_B @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.64  thf('19', plain, ((r2_hidden @ (sk_D_1 @ (sk_B @ sk_A)) @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '18'])).
% 0.46/0.64  thf(t7_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ~( ( r2_hidden @ A @ B ) & 
% 0.46/0.64          ( ![C:$i]:
% 0.46/0.64            ( ~( ( r2_hidden @ C @ B ) & 
% 0.46/0.64                 ( ![D:$i]:
% 0.46/0.64                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X9 @ X10) | (r2_hidden @ (sk_C @ X10) @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_tarski])).
% 0.46/0.64  thf('21', plain, ((r2_hidden @ (sk_C @ sk_A) @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X16 : $i]:
% 0.46/0.64         ((r2_hidden @ (sk_D_1 @ X16) @ sk_A)
% 0.46/0.64          | ~ (r2_hidden @ X16 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.46/0.64        | (r2_hidden @ (sk_D_1 @ (sk_C @ sk_A)) @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X9 @ X10) | (r2_hidden @ (sk_C @ X10) @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_tarski])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ X0) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '10'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ sk_A) @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.64  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('30', plain, ((r2_hidden @ (sk_C @ sk_A) @ sk_B_1)),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         ((v3_ordinal1 @ X12)
% 0.46/0.64          | ~ (v3_ordinal1 @ X13)
% 0.46/0.64          | ~ (r2_hidden @ X12 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ sk_B_1) | (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('34', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('35', plain, ((r2_hidden @ (sk_D_1 @ (sk_C @ sk_A)) @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['23', '34'])).
% 0.46/0.64  thf('36', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf(t26_ordinal1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.64           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ X14)
% 0.46/0.64          | (r1_ordinal1 @ X15 @ X14)
% 0.46/0.64          | (r2_hidden @ X14 @ X15)
% 0.46/0.64          | ~ (v3_ordinal1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X9 @ X10)
% 0.46/0.64          | ~ (r2_hidden @ X11 @ X10)
% 0.46/0.64          | ~ (r2_hidden @ X11 @ (sk_C @ X10)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_tarski])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X1 @ (sk_C @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('condensation', [status(thm)], ['38'])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v3_ordinal1 @ (sk_C @ X0))
% 0.46/0.64          | (r1_ordinal1 @ (sk_C @ X0) @ X1)
% 0.46/0.64          | ~ (v3_ordinal1 @ X1)
% 0.46/0.64          | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X0)
% 0.46/0.64          | (r1_ordinal1 @ (sk_C @ sk_A) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['36', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_D_1 @ (sk_C @ sk_A)))
% 0.46/0.64        | ~ (v3_ordinal1 @ (sk_D_1 @ (sk_C @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['35', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ X0) @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X16 : $i]:
% 0.46/0.64         ((v3_ordinal1 @ (sk_D_1 @ X16))
% 0.46/0.64          | ~ (r2_hidden @ X16 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      ((((sk_A) = (k1_xboole_0))
% 0.46/0.64        | ~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.46/0.64        | (v3_ordinal1 @ (sk_D_1 @ (sk_C @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.46/0.64        | (v3_ordinal1 @ (sk_D_1 @ (sk_C @ sk_A))))),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('49', plain, ((v3_ordinal1 @ (sk_D_1 @ (sk_C @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['47', '48'])).
% 0.46/0.64  thf('50', plain, ((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_D_1 @ (sk_C @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['42', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X16 : $i]:
% 0.46/0.64         (~ (r1_ordinal1 @ X16 @ (sk_D_1 @ X16))
% 0.46/0.64          | ~ (r2_hidden @ X16 @ sk_A)
% 0.46/0.64          | ~ (v3_ordinal1 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      ((~ (v3_ordinal1 @ (sk_C @ sk_A)) | ~ (r2_hidden @ (sk_C @ sk_A) @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('54', plain, ((r2_hidden @ (sk_C @ sk_A) @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('55', plain, ($false),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.48/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
