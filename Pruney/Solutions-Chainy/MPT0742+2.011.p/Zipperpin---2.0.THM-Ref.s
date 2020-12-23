%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NwuFe2qtmk

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:52 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 263 expanded)
%              Number of leaves         :   20 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  432 (2410 expanded)
%              Number of equality atoms :   17 ( 110 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
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

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
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
    ! [X18: $i] :
      ( ( r2_hidden @ ( sk_D @ X18 ) @ sk_A )
      | ~ ( r2_hidden @ X18 @ sk_A )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
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
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ sk_A ) ) @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C_1 @ sk_A ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('21',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('23',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['10','25'])).

thf('27',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( sk_C_1 @ X10 ) ) ) ),
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
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X18 ) )
      | ~ ( r2_hidden @ X18 @ sk_A )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
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
    inference(demod,[status(thm)],['23','24'])).

thf('40',plain,(
    v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X18: $i] :
      ( ~ ( r1_ordinal1 @ X18 @ ( sk_D @ X18 ) )
      | ~ ( r2_hidden @ X18 @ sk_A )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('45',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['10','25'])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('47',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['43','44','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NwuFe2qtmk
% 0.14/0.36  % Computer   : n005.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:33:48 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 252 iterations in 0.150s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(sk_D_type, type, sk_D: $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.61  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.61  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.44/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.61  thf('0', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.44/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.61  thf(t2_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.44/0.61       ( ( A ) = ( B ) ) ))).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (((X1) = (X0))
% 0.44/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.44/0.61          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.44/0.61      inference('cnf', [status(esa)], [t2_tarski])).
% 0.44/0.61  thf(t7_ordinal1, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X16 : $i, X17 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.44/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.44/0.61          | ((X1) = (X0))
% 0.44/0.61          | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['0', '3'])).
% 0.44/0.61  thf(t7_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ~( ( r2_hidden @ A @ B ) & 
% 0.44/0.61          ( ![C:$i]:
% 0.44/0.61            ( ~( ( r2_hidden @ C @ B ) & 
% 0.44/0.61                 ( ![D:$i]:
% 0.44/0.61                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.44/0.61  thf('5', plain,
% 0.44/0.61      (![X9 : $i, X10 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10) @ X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t7_tarski])).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.61  thf(t32_ordinal1, conjecture,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( v3_ordinal1 @ B ) =>
% 0.44/0.61       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.61            ( ![C:$i]:
% 0.44/0.61              ( ( v3_ordinal1 @ C ) =>
% 0.44/0.61                ( ~( ( r2_hidden @ C @ A ) & 
% 0.44/0.61                     ( ![D:$i]:
% 0.44/0.61                       ( ( v3_ordinal1 @ D ) =>
% 0.44/0.61                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i,B:$i]:
% 0.44/0.61        ( ( v3_ordinal1 @ B ) =>
% 0.44/0.61          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.61               ( ![C:$i]:
% 0.44/0.61                 ( ( v3_ordinal1 @ C ) =>
% 0.44/0.61                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.44/0.61                        ( ![D:$i]:
% 0.44/0.61                          ( ( v3_ordinal1 @ D ) =>
% 0.44/0.61                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.44/0.61  thf('7', plain,
% 0.44/0.61      (![X18 : $i]:
% 0.44/0.61         ((r2_hidden @ (sk_D @ X18) @ sk_A)
% 0.44/0.61          | ~ (r2_hidden @ X18 @ sk_A)
% 0.44/0.61          | ~ (v3_ordinal1 @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))
% 0.44/0.61        | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.44/0.61        | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.61  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.44/0.61        | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.44/0.61  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.61  thf(l1_zfmisc_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      (![X6 : $i, X8 : $i]:
% 0.44/0.61         ((r1_tarski @ (k1_tarski @ X6) @ X8) | ~ (r2_hidden @ X6 @ X8))),
% 0.44/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.44/0.61  thf('14', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((X0) = (k1_xboole_0))
% 0.44/0.61          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0)) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.61  thf(t1_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.44/0.61       ( r1_tarski @ A @ C ) ))).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.61         (~ (r1_tarski @ X2 @ X3)
% 0.44/0.61          | ~ (r1_tarski @ X3 @ X4)
% 0.44/0.61          | (r1_tarski @ X2 @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.44/0.61  thf('16', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (((X0) = (k1_xboole_0))
% 0.44/0.61          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0)) @ X1)
% 0.44/0.61          | ~ (r1_tarski @ X0 @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      (((r1_tarski @ (k1_tarski @ (sk_C_1 @ sk_A)) @ sk_B)
% 0.44/0.61        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['11', '16'])).
% 0.44/0.61  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('19', plain, ((r1_tarski @ (k1_tarski @ (sk_C_1 @ sk_A)) @ sk_B)),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (![X6 : $i, X7 : $i]:
% 0.44/0.61         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k1_tarski @ X6) @ X7))),
% 0.44/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.44/0.61  thf('21', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_B)),
% 0.44/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.61  thf(t23_ordinal1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      (![X12 : $i, X13 : $i]:
% 0.44/0.61         ((v3_ordinal1 @ X12)
% 0.44/0.61          | ~ (v3_ordinal1 @ X13)
% 0.44/0.61          | ~ (r2_hidden @ X12 @ X13))),
% 0.44/0.61      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.44/0.61  thf('23', plain,
% 0.44/0.61      ((~ (v3_ordinal1 @ sk_B) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.61  thf('24', plain, ((v3_ordinal1 @ sk_B)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('25', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf('26', plain, ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.44/0.61      inference('demod', [status(thm)], ['10', '25'])).
% 0.44/0.61  thf('27', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf(t26_ordinal1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.44/0.61           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X14 : $i, X15 : $i]:
% 0.44/0.61         (~ (v3_ordinal1 @ X14)
% 0.44/0.61          | (r1_ordinal1 @ X15 @ X14)
% 0.44/0.61          | (r2_hidden @ X14 @ X15)
% 0.44/0.61          | ~ (v3_ordinal1 @ X15))),
% 0.44/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X9 @ X10)
% 0.44/0.61          | ~ (r2_hidden @ X11 @ X10)
% 0.44/0.61          | ~ (r2_hidden @ X11 @ (sk_C_1 @ X10)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t7_tarski])).
% 0.44/0.61  thf('30', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.44/0.61      inference('condensation', [status(thm)], ['29'])).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (v3_ordinal1 @ (sk_C_1 @ X0))
% 0.44/0.61          | (r1_ordinal1 @ (sk_C_1 @ X0) @ X1)
% 0.44/0.61          | ~ (v3_ordinal1 @ X1)
% 0.44/0.61          | ~ (r2_hidden @ X1 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['28', '30'])).
% 0.44/0.61  thf('32', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X0 @ sk_A)
% 0.44/0.61          | ~ (v3_ordinal1 @ X0)
% 0.44/0.61          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['27', '31'])).
% 0.44/0.61  thf('33', plain,
% 0.44/0.61      (((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))
% 0.44/0.61        | ~ (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['26', '32'])).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (![X18 : $i]:
% 0.44/0.61         ((v3_ordinal1 @ (sk_D @ X18))
% 0.44/0.61          | ~ (r2_hidden @ X18 @ sk_A)
% 0.44/0.61          | ~ (v3_ordinal1 @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      ((((sk_A) = (k1_xboole_0))
% 0.44/0.61        | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.44/0.61        | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.61  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('38', plain,
% 0.44/0.61      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.44/0.61        | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.44/0.61      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.44/0.61  thf('39', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf('40', plain, ((v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      ((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.44/0.61      inference('demod', [status(thm)], ['33', '40'])).
% 0.44/0.61  thf('42', plain,
% 0.44/0.61      (![X18 : $i]:
% 0.44/0.61         (~ (r1_ordinal1 @ X18 @ (sk_D @ X18))
% 0.44/0.61          | ~ (r2_hidden @ X18 @ sk_A)
% 0.44/0.61          | ~ (v3_ordinal1 @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('43', plain,
% 0.44/0.61      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.44/0.61        | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.44/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.44/0.61  thf('44', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.44/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf('45', plain, ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.44/0.61      inference('demod', [status(thm)], ['10', '25'])).
% 0.44/0.61  thf('46', plain,
% 0.44/0.61      (![X9 : $i, X10 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10) @ X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t7_tarski])).
% 0.44/0.61  thf('47', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.44/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.61  thf('48', plain, ($false),
% 0.44/0.61      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
