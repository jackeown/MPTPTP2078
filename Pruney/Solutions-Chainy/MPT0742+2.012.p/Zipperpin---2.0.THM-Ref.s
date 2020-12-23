%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xyl6uS6wt6

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:52 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 209 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  511 (1974 expanded)
%              Number of equality atoms :   23 (  92 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_D @ X14 ) @ sk_A )
      | ~ ( r2_hidden @ X14 @ sk_A )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ sk_A ) ) @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C @ sk_A ) ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_tarski @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('17',plain,(
    r2_hidden @ ( sk_C @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

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
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_D @ ( sk_C @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['6','21'])).

thf('23',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
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
      | ~ ( r2_hidden @ X9 @ ( sk_C @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_D @ ( sk_C @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D @ ( sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X14 ) )
      | ~ ( r2_hidden @ X14 @ sk_A )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('36',plain,(
    v3_ordinal1 @ ( sk_D @ ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_ordinal1 @ ( sk_C @ sk_A ) @ ( sk_D @ ( sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X14: $i] :
      ( ~ ( r1_ordinal1 @ X14 @ ( sk_D @ X14 ) )
      | ~ ( r2_hidden @ X14 @ sk_A )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ ( sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('42',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_D @ X14 ) @ sk_A )
      | ~ ( r2_hidden @ X14 @ sk_A )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_tarski @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('56',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('58',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_ordinal1 @ ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r2_hidden @ ( sk_D @ ( sk_B @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','60'])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('63',plain,(
    r2_hidden @ ( sk_C @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xyl6uS6wt6
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 175 iterations in 0.127s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i > $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(sk_D_type, type, sk_D: $i > $i).
% 0.40/0.59  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.40/0.59  thf(t7_xboole_0, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.59  thf(t7_tarski, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ~( ( r2_hidden @ A @ B ) & 
% 0.40/0.59          ( ![C:$i]:
% 0.40/0.59            ( ~( ( r2_hidden @ C @ B ) & 
% 0.40/0.59                 ( ![D:$i]:
% 0.40/0.59                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C @ X8) @ X8))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_tarski])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ X0) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf(t32_ordinal1, conjecture,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( v3_ordinal1 @ B ) =>
% 0.40/0.59       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.59            ( ![C:$i]:
% 0.40/0.59              ( ( v3_ordinal1 @ C ) =>
% 0.40/0.59                ( ~( ( r2_hidden @ C @ A ) & 
% 0.40/0.59                     ( ![D:$i]:
% 0.40/0.59                       ( ( v3_ordinal1 @ D ) =>
% 0.40/0.59                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i]:
% 0.40/0.59        ( ( v3_ordinal1 @ B ) =>
% 0.40/0.59          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.59               ( ![C:$i]:
% 0.40/0.59                 ( ( v3_ordinal1 @ C ) =>
% 0.40/0.59                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.40/0.59                        ( ![D:$i]:
% 0.40/0.59                          ( ( v3_ordinal1 @ D ) =>
% 0.40/0.59                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (![X14 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_D @ X14) @ sk_A)
% 0.40/0.59          | ~ (r2_hidden @ X14 @ sk_A)
% 0.40/0.59          | ~ (v3_ordinal1 @ X14))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0))
% 0.40/0.59        | ~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.40/0.59        | (r2_hidden @ (sk_D @ (sk_C @ sk_A)) @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      ((~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.40/0.59        | (r2_hidden @ (sk_D @ (sk_C @ sk_A)) @ sk_A))),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ X0) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf(l1_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (![X4 : $i, X6 : $i]:
% 0.40/0.59         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_C @ X0)) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf(t1_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.40/0.59       ( r1_tarski @ A @ C ) ))).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X1 @ X2)
% 0.40/0.59          | ~ (r1_tarski @ X2 @ X3)
% 0.40/0.59          | (r1_tarski @ X1 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X0) = (k1_xboole_0))
% 0.40/0.59          | (r1_tarski @ (k1_tarski @ (sk_C @ X0)) @ X1)
% 0.40/0.59          | ~ (r1_tarski @ X0 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (((r1_tarski @ (k1_tarski @ (sk_C @ sk_A)) @ sk_B_1)
% 0.40/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['7', '12'])).
% 0.40/0.59  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('15', plain, ((r1_tarski @ (k1_tarski @ (sk_C @ sk_A)) @ sk_B_1)),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X4 : $i, X5 : $i]:
% 0.40/0.59         ((r2_hidden @ X4 @ X5) | ~ (r1_tarski @ (k1_tarski @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.59  thf('17', plain, ((r2_hidden @ (sk_C @ sk_A) @ sk_B_1)),
% 0.40/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.59  thf(t23_ordinal1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         ((v3_ordinal1 @ X10)
% 0.40/0.59          | ~ (v3_ordinal1 @ X11)
% 0.40/0.59          | ~ (r2_hidden @ X10 @ X11))),
% 0.40/0.59      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      ((~ (v3_ordinal1 @ sk_B_1) | (v3_ordinal1 @ (sk_C @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.59  thf('20', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('21', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('22', plain, ((r2_hidden @ (sk_D @ (sk_C @ sk_A)) @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['6', '21'])).
% 0.40/0.59  thf('23', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf(t26_ordinal1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.40/0.59           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i]:
% 0.40/0.59         (~ (v3_ordinal1 @ X12)
% 0.40/0.59          | (r1_ordinal1 @ X13 @ X12)
% 0.40/0.59          | (r2_hidden @ X12 @ X13)
% 0.40/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.40/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X7 @ X8)
% 0.40/0.59          | ~ (r2_hidden @ X9 @ X8)
% 0.40/0.59          | ~ (r2_hidden @ X9 @ (sk_C @ X8)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_tarski])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X1 @ (sk_C @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.59      inference('condensation', [status(thm)], ['25'])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (v3_ordinal1 @ (sk_C @ X0))
% 0.40/0.59          | (r1_ordinal1 @ (sk_C @ X0) @ X1)
% 0.40/0.59          | ~ (v3_ordinal1 @ X1)
% 0.40/0.59          | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['24', '26'])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.59          | ~ (v3_ordinal1 @ X0)
% 0.40/0.59          | (r1_ordinal1 @ (sk_C @ sk_A) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_D @ (sk_C @ sk_A)))
% 0.40/0.59        | ~ (v3_ordinal1 @ (sk_D @ (sk_C @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['22', '28'])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ X0) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X14 : $i]:
% 0.40/0.59         ((v3_ordinal1 @ (sk_D @ X14))
% 0.40/0.59          | ~ (r2_hidden @ X14 @ sk_A)
% 0.40/0.59          | ~ (v3_ordinal1 @ X14))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0))
% 0.40/0.59        | ~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.40/0.59        | (v3_ordinal1 @ (sk_D @ (sk_C @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.59  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      ((~ (v3_ordinal1 @ (sk_C @ sk_A))
% 0.40/0.59        | (v3_ordinal1 @ (sk_D @ (sk_C @ sk_A))))),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.40/0.59  thf('35', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('36', plain, ((v3_ordinal1 @ (sk_D @ (sk_C @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.59  thf('37', plain, ((r1_ordinal1 @ (sk_C @ sk_A) @ (sk_D @ (sk_C @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['29', '36'])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X14 : $i]:
% 0.40/0.59         (~ (r1_ordinal1 @ X14 @ (sk_D @ X14))
% 0.40/0.59          | ~ (r2_hidden @ X14 @ sk_A)
% 0.40/0.59          | ~ (v3_ordinal1 @ X14))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      ((~ (v3_ordinal1 @ (sk_C @ sk_A)) | ~ (r2_hidden @ (sk_C @ sk_A) @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.59  thf('40', plain, ((v3_ordinal1 @ (sk_C @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X14 : $i]:
% 0.40/0.59         ((r2_hidden @ (sk_D @ X14) @ sk_A)
% 0.40/0.59          | ~ (r2_hidden @ X14 @ sk_A)
% 0.40/0.59          | ~ (v3_ordinal1 @ X14))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      ((((sk_A) = (k1_xboole_0))
% 0.40/0.59        | ~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.40/0.59        | (r2_hidden @ (sk_D @ (sk_B @ sk_A)) @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.59  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      ((~ (v3_ordinal1 @ (sk_B @ sk_A))
% 0.40/0.59        | (r2_hidden @ (sk_D @ (sk_B @ sk_A)) @ sk_A))),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.40/0.59  thf('46', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X4 : $i, X6 : $i]:
% 0.40/0.59         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X1 @ X2)
% 0.40/0.59          | ~ (r1_tarski @ X2 @ X3)
% 0.40/0.59          | (r1_tarski @ X1 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X0) = (k1_xboole_0))
% 0.40/0.59          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X1)
% 0.40/0.59          | ~ (r1_tarski @ X0 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_1)
% 0.40/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['46', '51'])).
% 0.40/0.59  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('54', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_1)),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.40/0.59  thf('55', plain,
% 0.40/0.59      (![X4 : $i, X5 : $i]:
% 0.40/0.59         ((r2_hidden @ X4 @ X5) | ~ (r1_tarski @ (k1_tarski @ X4) @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.59  thf('56', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_1)),
% 0.40/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.40/0.59  thf('57', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         ((v3_ordinal1 @ X10)
% 0.40/0.59          | ~ (v3_ordinal1 @ X11)
% 0.40/0.59          | ~ (r2_hidden @ X10 @ X11))),
% 0.40/0.59      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.40/0.59  thf('58', plain,
% 0.40/0.59      ((~ (v3_ordinal1 @ sk_B_1) | (v3_ordinal1 @ (sk_B @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.40/0.59  thf('59', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('60', plain, ((v3_ordinal1 @ (sk_B @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['58', '59'])).
% 0.40/0.59  thf('61', plain, ((r2_hidden @ (sk_D @ (sk_B @ sk_A)) @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['45', '60'])).
% 0.40/0.59  thf('62', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C @ X8) @ X8))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_tarski])).
% 0.40/0.59  thf('63', plain, ((r2_hidden @ (sk_C @ sk_A) @ sk_A)),
% 0.40/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.40/0.59  thf('64', plain, ($false),
% 0.40/0.59      inference('demod', [status(thm)], ['39', '40', '63'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
