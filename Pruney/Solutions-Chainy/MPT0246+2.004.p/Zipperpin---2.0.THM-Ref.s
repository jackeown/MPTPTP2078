%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.flUpxTkJdP

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:14 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 156 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  601 (1207 expanded)
%              Number of equality atoms :   70 ( 139 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('1',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_A )
      | ( X33 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ X0 )
      | ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ sk_A )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','22'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('24',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ X0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B_1 )
        = ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ X0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ sk_B_1 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k1_tarski @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_A )
      | ( X33 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_1 @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( k1_xboole_0 = sk_A ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.flUpxTkJdP
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 369 iterations in 0.129s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(t3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]:
% 0.39/0.58         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.58  thf(t41_zfmisc_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.58          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i]:
% 0.39/0.58        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.58             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X33 : $i]: (~ (r2_hidden @ X33 @ sk_A) | ((X33) = (sk_B_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r1_xboole_0 @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]:
% 0.39/0.58         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ sk_B_1 @ X0)
% 0.39/0.58          | (r1_xboole_0 @ sk_A @ X0)
% 0.39/0.58          | (r1_xboole_0 @ sk_A @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ sk_B_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.58  thf(t83_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.39/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ sk_B_1 @ X0) | ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.58  thf(t48_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.39/0.58           = (k3_xboole_0 @ X17 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ X0))
% 0.39/0.58          | (r2_hidden @ sk_B_1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf(t7_xboole_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.39/0.58          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X12 : $i]:
% 0.39/0.58         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.58  thf(t3_boole, axiom,
% 0.39/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.58  thf('11', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.39/0.58           = (k3_xboole_0 @ X17 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.58  thf(d5_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.39/0.58       ( ![D:$i]:
% 0.39/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X6 @ X5)
% 0.39/0.58          | ~ (r2_hidden @ X6 @ X4)
% 0.39/0.58          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X6 @ X4)
% 0.39/0.58          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.39/0.58          | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '16'])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.39/0.58          | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '17'])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X6 @ X5)
% 0.39/0.58          | (r2_hidden @ X6 @ X3)
% 0.39/0.58          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.39/0.58         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.39/0.58      inference('clc', [status(thm)], ['18', '20'])).
% 0.39/0.58  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '21'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ X0))
% 0.39/0.58          | (r2_hidden @ sk_B_1 @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['9', '22'])).
% 0.39/0.58  thf(l1_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X28 : $i, X30 : $i]:
% 0.39/0.58         ((r1_tarski @ (k1_tarski @ X28) @ X30) | ~ (r2_hidden @ X28 @ X30))),
% 0.39/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ X0))
% 0.39/0.58          | (r1_tarski @ (k1_tarski @ sk_B_1) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.58  thf(l32_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X13 : $i, X15 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.39/0.58          | ~ (r1_tarski @ X13 @ X15))),
% 0.39/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ X0))
% 0.39/0.58          | ((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ X0) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.39/0.58           = (k3_xboole_0 @ X17 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0)
% 0.39/0.58            = (k3_xboole_0 @ (k1_tarski @ sk_B_1) @ X0))
% 0.39/0.58          | ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ X0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.39/0.58  thf('30', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_tarski @ sk_B_1) = (k3_xboole_0 @ (k1_tarski @ sk_B_1) @ X0))
% 0.39/0.58          | ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k3_xboole_0 @ X0 @ (k1_tarski @ sk_B_1)) = (k1_tarski @ sk_B_1))
% 0.39/0.58          | ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ X0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '21'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i]:
% 0.39/0.58         ((r1_tarski @ X13 @ X14)
% 0.39/0.58          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.58  thf('37', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.39/0.58      inference('simplify', [status(thm)], ['36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (![X28 : $i, X29 : $i]:
% 0.39/0.58         ((r2_hidden @ X28 @ X29) | ~ (r1_tarski @ (k1_tarski @ X28) @ X29))),
% 0.39/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.58  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (![X12 : $i]:
% 0.39/0.58         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.39/0.58         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.58          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (![X33 : $i]: (~ (r2_hidden @ X33 @ sk_A) | ((X33) = (sk_B_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.39/0.58          | ((sk_B @ (k4_xboole_0 @ sk_A @ X0)) = (sk_B_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (![X12 : $i]:
% 0.39/0.58         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X6 @ X4)
% 0.39/0.58          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.39/0.58          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r2_hidden @ sk_B_1 @ X0)
% 0.39/0.58          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.39/0.58          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['44', '47'])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0))
% 0.39/0.58          | ~ (r2_hidden @ sk_B_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['39', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.39/0.58           = (k3_xboole_0 @ X17 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.39/0.58         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('53', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.58  thf('54', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.39/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.39/0.58        | ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_A)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['33', '54'])).
% 0.39/0.58  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '21'])).
% 0.39/0.58  thf('57', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.39/0.58           = (k3_xboole_0 @ X17 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['56', '57'])).
% 0.39/0.58  thf('59', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.58  thf('60', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      ((((sk_A) = (k1_tarski @ sk_B_1)) | ((k1_xboole_0) = (sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['55', '60'])).
% 0.39/0.58  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('63', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('64', plain, ($false),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['61', '62', '63'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
