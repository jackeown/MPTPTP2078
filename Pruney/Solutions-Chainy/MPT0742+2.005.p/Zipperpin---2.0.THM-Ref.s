%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d71T8zx9RC

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:51 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 437 expanded)
%              Number of leaves         :   22 ( 140 expanded)
%              Depth                    :   19
%              Number of atoms          :  525 (5096 expanded)
%              Number of equality atoms :    9 ( 148 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_tarski_type,type,(
    r2_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ X12 )
      | ( r1_tarski @ X13 @ ( k1_setfam_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

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
    ! [X21: $i] :
      ( ( r2_hidden @ ( sk_D @ X21 ) @ sk_A )
      | ~ ( r2_hidden @ X21 @ sk_A )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v3_ordinal1 @ ( sk_C_2 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C_2 @ X0 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ ( sk_C_2 @ X0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C_2 @ X0 @ sk_A ) ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ X12 )
      | ( r1_tarski @ X13 @ ( k1_setfam_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

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

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ( v3_ordinal1 @ ( sk_C_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( v3_ordinal1 @ ( sk_C_2 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( sk_C_2 @ X0 @ sk_A ) ) @ sk_A )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['4','15'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t136_zfmisc_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ~ ( ( r1_tarski @ C @ B )
            & ~ ( r2_tarski @ C @ B )
            & ~ ( r2_hidden @ C @ B ) )
      & ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) )
      & ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ C @ B )
            & ( r1_tarski @ D @ C ) )
         => ( r2_hidden @ D @ B ) )
      & ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( sk_B @ X4 ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( sk_B @ X4 ) )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r2_hidden @ X6 @ ( sk_B @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_B @ ( k1_setfam_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( sk_B @ X4 ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf('24',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( sk_B @ X4 ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf(t3_ordinal1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ B @ C )
        & ( r2_hidden @ C @ A ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_ordinal1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( sk_B @ ( sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X21: $i] :
      ( ( r2_hidden @ ( sk_D @ X21 ) @ sk_A )
      | ~ ( r2_hidden @ X21 @ sk_A )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','27'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('33',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('35',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( r1_ordinal1 @ X17 @ X16 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( sk_C_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) )
    | ~ ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','27'])).

thf('47',plain,(
    ! [X21: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X21 ) )
      | ~ ( r2_hidden @ X21 @ sk_A )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('50',plain,(
    v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X21: $i] :
      ( ~ ( r1_ordinal1 @ X21 @ ( sk_D @ X21 ) )
      | ~ ( r2_hidden @ X21 @ sk_A )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('55',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','27'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d71T8zx9RC
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:28:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.71  % Solved by: fo/fo7.sh
% 0.45/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.71  % done 402 iterations in 0.244s
% 0.45/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.71  % SZS output start Refutation
% 0.45/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.71  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.45/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.71  thf(sk_D_type, type, sk_D: $i > $i).
% 0.45/0.71  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.45/0.71  thf(r2_tarski_type, type, r2_tarski: $i > $i > $o).
% 0.45/0.71  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.71  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.45/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.71  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.71  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.45/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.71  thf(t6_setfam_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.45/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.45/0.71  thf('0', plain,
% 0.45/0.71      (![X12 : $i, X13 : $i]:
% 0.45/0.71         (((X12) = (k1_xboole_0))
% 0.45/0.71          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ X12)
% 0.45/0.71          | (r1_tarski @ X13 @ (k1_setfam_1 @ X12)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.45/0.71  thf(t32_ordinal1, conjecture,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( v3_ordinal1 @ B ) =>
% 0.45/0.71       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.71            ( ![C:$i]:
% 0.45/0.71              ( ( v3_ordinal1 @ C ) =>
% 0.45/0.71                ( ~( ( r2_hidden @ C @ A ) & 
% 0.45/0.71                     ( ![D:$i]:
% 0.45/0.71                       ( ( v3_ordinal1 @ D ) =>
% 0.45/0.71                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.71    (~( ![A:$i,B:$i]:
% 0.45/0.71        ( ( v3_ordinal1 @ B ) =>
% 0.45/0.71          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.71               ( ![C:$i]:
% 0.45/0.71                 ( ( v3_ordinal1 @ C ) =>
% 0.45/0.71                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.45/0.71                        ( ![D:$i]:
% 0.45/0.71                          ( ( v3_ordinal1 @ D ) =>
% 0.45/0.71                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.71    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.45/0.71  thf('1', plain,
% 0.45/0.71      (![X21 : $i]:
% 0.45/0.71         ((r2_hidden @ (sk_D @ X21) @ sk_A)
% 0.45/0.71          | ~ (r2_hidden @ X21 @ sk_A)
% 0.45/0.71          | ~ (v3_ordinal1 @ X21))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('2', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.45/0.71          | ((sk_A) = (k1_xboole_0))
% 0.45/0.71          | ~ (v3_ordinal1 @ (sk_C_2 @ X0 @ sk_A))
% 0.45/0.71          | (r2_hidden @ (sk_D @ (sk_C_2 @ X0 @ sk_A)) @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.71  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('4', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.45/0.71          | ~ (v3_ordinal1 @ (sk_C_2 @ X0 @ sk_A))
% 0.45/0.71          | (r2_hidden @ (sk_D @ (sk_C_2 @ X0 @ sk_A)) @ sk_A))),
% 0.45/0.71      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.45/0.71  thf('5', plain,
% 0.45/0.71      (![X12 : $i, X13 : $i]:
% 0.45/0.71         (((X12) = (k1_xboole_0))
% 0.45/0.71          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ X12)
% 0.45/0.71          | (r1_tarski @ X13 @ (k1_setfam_1 @ X12)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.45/0.71  thf('6', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(d3_tarski, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.71  thf('7', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.71          | (r2_hidden @ X0 @ X2)
% 0.45/0.71          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.71  thf('8', plain,
% 0.45/0.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.71  thf('9', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.45/0.71          | ((sk_A) = (k1_xboole_0))
% 0.45/0.71          | (r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ sk_B_1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['5', '8'])).
% 0.45/0.71  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('11', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.45/0.71          | (r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ sk_B_1))),
% 0.45/0.71      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.45/0.71  thf(t23_ordinal1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.45/0.71  thf('12', plain,
% 0.45/0.71      (![X14 : $i, X15 : $i]:
% 0.45/0.71         ((v3_ordinal1 @ X14)
% 0.45/0.71          | ~ (v3_ordinal1 @ X15)
% 0.45/0.71          | ~ (r2_hidden @ X14 @ X15))),
% 0.45/0.71      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.45/0.71  thf('13', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.45/0.71          | ~ (v3_ordinal1 @ sk_B_1)
% 0.45/0.71          | (v3_ordinal1 @ (sk_C_2 @ X0 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.71  thf('14', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('15', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.45/0.71          | (v3_ordinal1 @ (sk_C_2 @ X0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.71  thf('16', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r2_hidden @ (sk_D @ (sk_C_2 @ X0 @ sk_A)) @ sk_A)
% 0.45/0.71          | (r1_tarski @ X0 @ (k1_setfam_1 @ sk_A)))),
% 0.45/0.71      inference('clc', [status(thm)], ['4', '15'])).
% 0.45/0.71  thf(t7_tarski, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ~( ( r2_hidden @ A @ B ) & 
% 0.45/0.71          ( ![C:$i]:
% 0.45/0.71            ( ~( ( r2_hidden @ C @ B ) & 
% 0.45/0.71                 ( ![D:$i]:
% 0.45/0.71                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.45/0.71  thf('17', plain,
% 0.45/0.71      (![X9 : $i, X10 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10) @ X10))),
% 0.45/0.71      inference('cnf', [status(esa)], [t7_tarski])).
% 0.45/0.71  thf('18', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.45/0.71          | (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.71  thf(t136_zfmisc_1, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ?[B:$i]:
% 0.45/0.71       ( ( ![C:$i]:
% 0.45/0.71           ( ~( ( r1_tarski @ C @ B ) & ( ~( r2_tarski @ C @ B ) ) & 
% 0.45/0.71                ( ~( r2_hidden @ C @ B ) ) ) ) ) & 
% 0.45/0.71         ( ![C:$i]:
% 0.45/0.71           ( ( r2_hidden @ C @ B ) => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) ) ) & 
% 0.45/0.71         ( ![C:$i,D:$i]:
% 0.45/0.71           ( ( ( r2_hidden @ C @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.45/0.71             ( r2_hidden @ D @ B ) ) ) & 
% 0.45/0.71         ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.71  thf('19', plain, (![X4 : $i]: (r2_hidden @ X4 @ (sk_B @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [t136_zfmisc_1])).
% 0.45/0.71  thf('20', plain,
% 0.45/0.71      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X5 @ (sk_B @ X4))
% 0.45/0.71          | ~ (r1_tarski @ X6 @ X5)
% 0.45/0.71          | (r2_hidden @ X6 @ (sk_B @ X4)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t136_zfmisc_1])).
% 0.45/0.71  thf('21', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         ((r2_hidden @ X1 @ (sk_B @ X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.45/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.71  thf('22', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)
% 0.45/0.71          | (r2_hidden @ X0 @ (sk_B @ (k1_setfam_1 @ sk_A))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['18', '21'])).
% 0.45/0.71  thf('23', plain, (![X4 : $i]: (r2_hidden @ X4 @ (sk_B @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [t136_zfmisc_1])).
% 0.45/0.71  thf('24', plain, (![X4 : $i]: (r2_hidden @ X4 @ (sk_B @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [t136_zfmisc_1])).
% 0.45/0.71  thf(t3_ordinal1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ~( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) & ( r2_hidden @ C @ A ) ) ))).
% 0.45/0.71  thf('25', plain,
% 0.45/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X18 @ X19)
% 0.45/0.71          | ~ (r2_hidden @ X20 @ X18)
% 0.45/0.71          | ~ (r2_hidden @ X19 @ X20))),
% 0.45/0.71      inference('cnf', [status(esa)], [t3_ordinal1])).
% 0.45/0.71  thf('26', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (r2_hidden @ (sk_B @ X0) @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.71  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ (sk_B @ (sk_B @ X0)) @ X0)),
% 0.45/0.71      inference('sup-', [status(thm)], ['23', '26'])).
% 0.45/0.71  thf('28', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['22', '27'])).
% 0.45/0.71  thf('29', plain,
% 0.45/0.71      (![X21 : $i]:
% 0.45/0.71         ((r2_hidden @ (sk_D @ X21) @ sk_A)
% 0.45/0.71          | ~ (r2_hidden @ X21 @ sk_A)
% 0.45/0.71          | ~ (v3_ordinal1 @ X21))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('30', plain,
% 0.45/0.71      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.45/0.71        | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.71  thf('31', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['22', '27'])).
% 0.45/0.71  thf('32', plain,
% 0.45/0.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.71  thf('33', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_B_1)),
% 0.45/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.71  thf('34', plain,
% 0.45/0.71      (![X14 : $i, X15 : $i]:
% 0.45/0.71         ((v3_ordinal1 @ X14)
% 0.45/0.71          | ~ (v3_ordinal1 @ X15)
% 0.45/0.71          | ~ (r2_hidden @ X14 @ X15))),
% 0.45/0.71      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.45/0.71  thf('35', plain,
% 0.45/0.71      ((~ (v3_ordinal1 @ sk_B_1) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.71  thf('36', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('37', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.71  thf('38', plain, ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)),
% 0.45/0.71      inference('demod', [status(thm)], ['30', '37'])).
% 0.45/0.71  thf('39', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.71  thf(t26_ordinal1, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( v3_ordinal1 @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( v3_ordinal1 @ B ) =>
% 0.45/0.71           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.71  thf('40', plain,
% 0.45/0.71      (![X16 : $i, X17 : $i]:
% 0.45/0.71         (~ (v3_ordinal1 @ X16)
% 0.45/0.71          | (r1_ordinal1 @ X17 @ X16)
% 0.45/0.71          | (r2_hidden @ X16 @ X17)
% 0.45/0.71          | ~ (v3_ordinal1 @ X17))),
% 0.45/0.71      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.45/0.71  thf('41', plain,
% 0.45/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X9 @ X10)
% 0.45/0.71          | ~ (r2_hidden @ X11 @ X10)
% 0.45/0.71          | ~ (r2_hidden @ X11 @ (sk_C_1 @ X10)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t7_tarski])).
% 0.45/0.71  thf('42', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.71      inference('condensation', [status(thm)], ['41'])).
% 0.45/0.71  thf('43', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (v3_ordinal1 @ (sk_C_1 @ X0))
% 0.45/0.71          | (r1_ordinal1 @ (sk_C_1 @ X0) @ X1)
% 0.45/0.71          | ~ (v3_ordinal1 @ X1)
% 0.45/0.71          | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.71      inference('sup-', [status(thm)], ['40', '42'])).
% 0.45/0.71  thf('44', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X0 @ sk_A)
% 0.45/0.71          | ~ (v3_ordinal1 @ X0)
% 0.45/0.71          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ X0))),
% 0.45/0.71      inference('sup-', [status(thm)], ['39', '43'])).
% 0.45/0.71  thf('45', plain,
% 0.45/0.71      (((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))
% 0.45/0.71        | ~ (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['38', '44'])).
% 0.45/0.71  thf('46', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['22', '27'])).
% 0.45/0.71  thf('47', plain,
% 0.45/0.71      (![X21 : $i]:
% 0.45/0.71         ((v3_ordinal1 @ (sk_D @ X21))
% 0.45/0.71          | ~ (r2_hidden @ X21 @ sk_A)
% 0.45/0.71          | ~ (v3_ordinal1 @ X21))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('48', plain,
% 0.45/0.71      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.45/0.71        | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.45/0.71      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.71  thf('49', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.71  thf('50', plain, ((v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['48', '49'])).
% 0.45/0.71  thf('51', plain,
% 0.45/0.71      ((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['45', '50'])).
% 0.45/0.71  thf('52', plain,
% 0.45/0.71      (![X21 : $i]:
% 0.45/0.71         (~ (r1_ordinal1 @ X21 @ (sk_D @ X21))
% 0.45/0.71          | ~ (r2_hidden @ X21 @ sk_A)
% 0.45/0.71          | ~ (v3_ordinal1 @ X21))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('53', plain,
% 0.45/0.71      ((~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.45/0.71        | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.71  thf('54', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.71  thf('55', plain, ((r2_hidden @ (sk_C_1 @ sk_A) @ sk_A)),
% 0.45/0.71      inference('sup-', [status(thm)], ['22', '27'])).
% 0.45/0.71  thf('56', plain, ($false),
% 0.45/0.71      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.45/0.71  
% 0.45/0.71  % SZS output end Refutation
% 0.45/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
