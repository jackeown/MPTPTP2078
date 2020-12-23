%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7OVKSprr7j

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:37 EST 2020

% Result     : Theorem 7.03s
% Output     : Refutation 7.03s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 515 expanded)
%              Number of leaves         :   21 ( 154 expanded)
%              Depth                    :   29
%              Number of atoms          :  787 (5441 expanded)
%              Number of equality atoms :   65 ( 623 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('0',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
    | ( k1_xboole_0 = sk_B )
    | ( k1_xboole_0 = sk_A ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( r1_tarski @ sk_D @ sk_B )
    | ( r1_tarski @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference(simplify,[status(thm)],['27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ( sk_B = sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X19 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('39',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference(simplify,[status(thm)],['27'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X24 @ X22 ) @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X20 @ X19 ) @ ( k2_zfmisc_1 @ X21 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ X0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_A ) ),
    inference(eq_fact,[status(thm)],['50'])).

thf('52',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14'])).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('54',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) @ sk_D ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_C_2 = sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ ( sk_C_1 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_C_2 = sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('63',plain,
    ( ( sk_C_2 = sk_A )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_A ) ),
    inference(eq_fact,[status(thm)],['50'])).

thf('66',plain,(
    sk_C_2 = sk_A ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C_2 @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['37','66'])).

thf('68',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['32','67'])).

thf('69',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['30','68'])).

thf('70',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,(
    sk_C_2 = sk_A ),
    inference(clc,[status(thm)],['64','65'])).

thf('73',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['70'])).

thf('74',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A = sk_C_2 ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['70'])).

thf('77',plain,(
    sk_B != sk_D ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    sk_B != sk_D ),
    inference(simpl_trail,[status(thm)],['71','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7OVKSprr7j
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 7.03/7.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.03/7.21  % Solved by: fo/fo7.sh
% 7.03/7.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.03/7.21  % done 3724 iterations in 6.759s
% 7.03/7.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.03/7.21  % SZS output start Refutation
% 7.03/7.21  thf(sk_D_type, type, sk_D: $i).
% 7.03/7.21  thf(sk_B_type, type, sk_B: $i).
% 7.03/7.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.03/7.21  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 7.03/7.21  thf(sk_A_type, type, sk_A: $i).
% 7.03/7.21  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 7.03/7.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.03/7.21  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 7.03/7.21  thf(sk_C_2_type, type, sk_C_2: $i).
% 7.03/7.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.03/7.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.03/7.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.03/7.21  thf(t134_zfmisc_1, conjecture,
% 7.03/7.21    (![A:$i,B:$i,C:$i,D:$i]:
% 7.03/7.21     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 7.03/7.21       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.03/7.21         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 7.03/7.21  thf(zf_stmt_0, negated_conjecture,
% 7.03/7.21    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 7.03/7.21        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 7.03/7.21          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.03/7.21            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 7.03/7.21    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 7.03/7.21  thf('0', plain,
% 7.03/7.21      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf(t2_tarski, axiom,
% 7.03/7.21    (![A:$i,B:$i]:
% 7.03/7.21     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 7.03/7.21       ( ( A ) = ( B ) ) ))).
% 7.03/7.21  thf('1', plain,
% 7.03/7.21      (![X8 : $i, X9 : $i]:
% 7.03/7.21         (((X9) = (X8))
% 7.03/7.21          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 7.03/7.21          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X9))),
% 7.03/7.21      inference('cnf', [status(esa)], [t2_tarski])).
% 7.03/7.21  thf(t5_boole, axiom,
% 7.03/7.21    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.03/7.21  thf('2', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 7.03/7.21      inference('cnf', [status(esa)], [t5_boole])).
% 7.03/7.21  thf(t1_xboole_0, axiom,
% 7.03/7.21    (![A:$i,B:$i,C:$i]:
% 7.03/7.21     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 7.03/7.21       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 7.03/7.21  thf('3', plain,
% 7.03/7.21      (![X4 : $i, X5 : $i, X6 : $i]:
% 7.03/7.21         (~ (r2_hidden @ X4 @ X5)
% 7.03/7.21          | ~ (r2_hidden @ X4 @ X6)
% 7.03/7.21          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 7.03/7.21      inference('cnf', [status(esa)], [t1_xboole_0])).
% 7.03/7.21  thf('4', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i]:
% 7.03/7.21         (~ (r2_hidden @ X1 @ X0)
% 7.03/7.21          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 7.03/7.21          | ~ (r2_hidden @ X1 @ X0))),
% 7.03/7.21      inference('sup-', [status(thm)], ['2', '3'])).
% 7.03/7.21  thf('5', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i]:
% 7.03/7.21         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 7.03/7.21      inference('simplify', [status(thm)], ['4'])).
% 7.03/7.21  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 7.03/7.21      inference('condensation', [status(thm)], ['5'])).
% 7.03/7.21  thf('7', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 7.03/7.21          | ((k1_xboole_0) = (X0)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['1', '6'])).
% 7.03/7.21  thf('8', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 7.03/7.21          | ((k1_xboole_0) = (X0)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['1', '6'])).
% 7.03/7.21  thf(l54_zfmisc_1, axiom,
% 7.03/7.21    (![A:$i,B:$i,C:$i,D:$i]:
% 7.03/7.21     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 7.03/7.21       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 7.03/7.21  thf('9', plain,
% 7.03/7.21      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 7.03/7.21         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 7.03/7.21          | ~ (r2_hidden @ X16 @ X18)
% 7.03/7.21          | ~ (r2_hidden @ X14 @ X15))),
% 7.03/7.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.03/7.21  thf('10', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.03/7.21         (((k1_xboole_0) = (X0))
% 7.03/7.21          | ~ (r2_hidden @ X2 @ X1)
% 7.03/7.21          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ X0 @ k1_xboole_0)) @ 
% 7.03/7.21             (k2_zfmisc_1 @ X1 @ X0)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['8', '9'])).
% 7.03/7.21  thf('11', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i]:
% 7.03/7.21         (((k1_xboole_0) = (X0))
% 7.03/7.21          | (r2_hidden @ 
% 7.03/7.21             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 7.03/7.21              (sk_C_1 @ X1 @ k1_xboole_0)) @ 
% 7.03/7.21             (k2_zfmisc_1 @ X0 @ X1))
% 7.03/7.21          | ((k1_xboole_0) = (X1)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['7', '10'])).
% 7.03/7.21  thf('12', plain,
% 7.03/7.21      (((r2_hidden @ 
% 7.03/7.21         (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 7.03/7.21          (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 7.03/7.21         (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 7.03/7.21        | ((k1_xboole_0) = (sk_B))
% 7.03/7.21        | ((k1_xboole_0) = (sk_A)))),
% 7.03/7.21      inference('sup+', [status(thm)], ['0', '11'])).
% 7.03/7.21  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf('15', plain,
% 7.03/7.21      ((r2_hidden @ 
% 7.03/7.21        (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 7.03/7.21         (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 7.03/7.21        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 7.03/7.21      inference('simplify_reflect-', [status(thm)], ['12', '13', '14'])).
% 7.03/7.21  thf('16', plain,
% 7.03/7.21      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 7.03/7.21         ((r2_hidden @ X14 @ X15)
% 7.03/7.21          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 7.03/7.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.03/7.21  thf('17', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ k1_xboole_0) @ sk_C_2)),
% 7.03/7.21      inference('sup-', [status(thm)], ['15', '16'])).
% 7.03/7.21  thf(d3_tarski, axiom,
% 7.03/7.21    (![A:$i,B:$i]:
% 7.03/7.21     ( ( r1_tarski @ A @ B ) <=>
% 7.03/7.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.03/7.21  thf('18', plain,
% 7.03/7.21      (![X1 : $i, X3 : $i]:
% 7.03/7.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.03/7.21      inference('cnf', [status(esa)], [d3_tarski])).
% 7.03/7.21  thf('19', plain,
% 7.03/7.21      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 7.03/7.21         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 7.03/7.21          | ~ (r2_hidden @ X16 @ X18)
% 7.03/7.21          | ~ (r2_hidden @ X14 @ X15))),
% 7.03/7.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.03/7.21  thf('20', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.03/7.21         ((r1_tarski @ X0 @ X1)
% 7.03/7.21          | ~ (r2_hidden @ X3 @ X2)
% 7.03/7.21          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 7.03/7.21             (k2_zfmisc_1 @ X2 @ X0)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['18', '19'])).
% 7.03/7.21  thf('21', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i]:
% 7.03/7.21         ((r2_hidden @ 
% 7.03/7.21           (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ (sk_C @ X1 @ X0)) @ 
% 7.03/7.21           (k2_zfmisc_1 @ sk_C_2 @ X0))
% 7.03/7.21          | (r1_tarski @ X0 @ X1))),
% 7.03/7.21      inference('sup-', [status(thm)], ['17', '20'])).
% 7.03/7.21  thf('22', plain,
% 7.03/7.21      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf('23', plain,
% 7.03/7.21      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 7.03/7.21         ((r2_hidden @ X16 @ X17)
% 7.03/7.21          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 7.03/7.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.03/7.21  thf('24', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i]:
% 7.03/7.21         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 7.03/7.21          | (r2_hidden @ X0 @ sk_B))),
% 7.03/7.21      inference('sup-', [status(thm)], ['22', '23'])).
% 7.03/7.21  thf('25', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         ((r1_tarski @ sk_D @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_B))),
% 7.03/7.21      inference('sup-', [status(thm)], ['21', '24'])).
% 7.03/7.21  thf('26', plain,
% 7.03/7.21      (![X1 : $i, X3 : $i]:
% 7.03/7.21         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.03/7.21      inference('cnf', [status(esa)], [d3_tarski])).
% 7.03/7.21  thf('27', plain, (((r1_tarski @ sk_D @ sk_B) | (r1_tarski @ sk_D @ sk_B))),
% 7.03/7.21      inference('sup-', [status(thm)], ['25', '26'])).
% 7.03/7.21  thf('28', plain, ((r1_tarski @ sk_D @ sk_B)),
% 7.03/7.21      inference('simplify', [status(thm)], ['27'])).
% 7.03/7.21  thf(d10_xboole_0, axiom,
% 7.03/7.21    (![A:$i,B:$i]:
% 7.03/7.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.03/7.21  thf('29', plain,
% 7.03/7.21      (![X10 : $i, X12 : $i]:
% 7.03/7.21         (((X10) = (X12))
% 7.03/7.21          | ~ (r1_tarski @ X12 @ X10)
% 7.03/7.21          | ~ (r1_tarski @ X10 @ X12))),
% 7.03/7.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.03/7.21  thf('30', plain, ((~ (r1_tarski @ sk_B @ sk_D) | ((sk_B) = (sk_D)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['28', '29'])).
% 7.03/7.21  thf('31', plain,
% 7.03/7.21      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 7.03/7.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.03/7.21  thf('32', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 7.03/7.21      inference('simplify', [status(thm)], ['31'])).
% 7.03/7.21  thf('33', plain,
% 7.03/7.21      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf(t117_zfmisc_1, axiom,
% 7.03/7.21    (![A:$i,B:$i,C:$i]:
% 7.03/7.21     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 7.03/7.21          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 7.03/7.21            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 7.03/7.21          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 7.03/7.21  thf('34', plain,
% 7.03/7.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.03/7.21         (((X19) = (k1_xboole_0))
% 7.03/7.21          | (r1_tarski @ X20 @ X21)
% 7.03/7.21          | ~ (r1_tarski @ (k2_zfmisc_1 @ X19 @ X20) @ 
% 7.03/7.21               (k2_zfmisc_1 @ X19 @ X21)))),
% 7.03/7.21      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 7.03/7.21  thf('35', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 7.03/7.21             (k2_zfmisc_1 @ sk_A @ X0))
% 7.03/7.21          | (r1_tarski @ sk_B @ X0)
% 7.03/7.21          | ((sk_A) = (k1_xboole_0)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['33', '34'])).
% 7.03/7.21  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf('37', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 7.03/7.21             (k2_zfmisc_1 @ sk_A @ X0))
% 7.03/7.21          | (r1_tarski @ sk_B @ X0))),
% 7.03/7.21      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 7.03/7.21  thf('38', plain,
% 7.03/7.21      (![X8 : $i, X9 : $i]:
% 7.03/7.21         (((X9) = (X8))
% 7.03/7.21          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 7.03/7.21          | (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X9))),
% 7.03/7.21      inference('cnf', [status(esa)], [t2_tarski])).
% 7.03/7.21  thf('39', plain, ((r1_tarski @ sk_D @ sk_B)),
% 7.03/7.21      inference('simplify', [status(thm)], ['27'])).
% 7.03/7.21  thf(t118_zfmisc_1, axiom,
% 7.03/7.21    (![A:$i,B:$i,C:$i]:
% 7.03/7.21     ( ( r1_tarski @ A @ B ) =>
% 7.03/7.21       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 7.03/7.21         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 7.03/7.21  thf('40', plain,
% 7.03/7.21      (![X22 : $i, X23 : $i, X24 : $i]:
% 7.03/7.21         (~ (r1_tarski @ X22 @ X23)
% 7.03/7.21          | (r1_tarski @ (k2_zfmisc_1 @ X24 @ X22) @ (k2_zfmisc_1 @ X24 @ X23)))),
% 7.03/7.21      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 7.03/7.21  thf('41', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ X0 @ sk_B))),
% 7.03/7.21      inference('sup-', [status(thm)], ['39', '40'])).
% 7.03/7.21  thf('42', plain,
% 7.03/7.21      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf('43', plain,
% 7.03/7.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.03/7.21         (((X19) = (k1_xboole_0))
% 7.03/7.21          | (r1_tarski @ X20 @ X21)
% 7.03/7.21          | ~ (r1_tarski @ (k2_zfmisc_1 @ X20 @ X19) @ 
% 7.03/7.21               (k2_zfmisc_1 @ X21 @ X19)))),
% 7.03/7.21      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 7.03/7.21  thf('44', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 7.03/7.21             (k2_zfmisc_1 @ X0 @ sk_B))
% 7.03/7.21          | (r1_tarski @ sk_A @ X0)
% 7.03/7.21          | ((sk_B) = (k1_xboole_0)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['42', '43'])).
% 7.03/7.21  thf('45', plain, (((sk_B) != (k1_xboole_0))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf('46', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 7.03/7.21             (k2_zfmisc_1 @ X0 @ sk_B))
% 7.03/7.21          | (r1_tarski @ sk_A @ X0))),
% 7.03/7.21      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 7.03/7.21  thf('47', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 7.03/7.21      inference('sup-', [status(thm)], ['41', '46'])).
% 7.03/7.21  thf('48', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.03/7.21         (~ (r2_hidden @ X0 @ X1)
% 7.03/7.21          | (r2_hidden @ X0 @ X2)
% 7.03/7.21          | ~ (r1_tarski @ X1 @ X2))),
% 7.03/7.21      inference('cnf', [status(esa)], [d3_tarski])).
% 7.03/7.21  thf('49', plain,
% 7.03/7.21      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 7.03/7.21      inference('sup-', [status(thm)], ['47', '48'])).
% 7.03/7.21  thf('50', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         ((r2_hidden @ (sk_C_1 @ sk_A @ X0) @ X0)
% 7.03/7.21          | ((X0) = (sk_A))
% 7.03/7.21          | (r2_hidden @ (sk_C_1 @ sk_A @ X0) @ sk_C_2))),
% 7.03/7.21      inference('sup-', [status(thm)], ['38', '49'])).
% 7.03/7.21  thf('51', plain,
% 7.03/7.21      (((r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2) | ((sk_C_2) = (sk_A)))),
% 7.03/7.21      inference('eq_fact', [status(thm)], ['50'])).
% 7.03/7.21  thf('52', plain,
% 7.03/7.21      ((r2_hidden @ 
% 7.03/7.21        (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 7.03/7.21         (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 7.03/7.21        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 7.03/7.21      inference('simplify_reflect-', [status(thm)], ['12', '13', '14'])).
% 7.03/7.21  thf('53', plain,
% 7.03/7.21      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 7.03/7.21         ((r2_hidden @ X16 @ X17)
% 7.03/7.21          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 7.03/7.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.03/7.21  thf('54', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ k1_xboole_0) @ sk_D)),
% 7.03/7.21      inference('sup-', [status(thm)], ['52', '53'])).
% 7.03/7.21  thf('55', plain,
% 7.03/7.21      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 7.03/7.21         ((r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X18))
% 7.03/7.21          | ~ (r2_hidden @ X16 @ X18)
% 7.03/7.21          | ~ (r2_hidden @ X14 @ X15))),
% 7.03/7.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.03/7.21  thf('56', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i]:
% 7.03/7.21         (~ (r2_hidden @ X1 @ X0)
% 7.03/7.21          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 7.03/7.21             (k2_zfmisc_1 @ X0 @ sk_D)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['54', '55'])).
% 7.03/7.21  thf('57', plain,
% 7.03/7.21      ((((sk_C_2) = (sk_A))
% 7.03/7.21        | (r2_hidden @ 
% 7.03/7.21           (k4_tarski @ (sk_C_1 @ sk_A @ sk_C_2) @ 
% 7.03/7.21            (sk_C_1 @ sk_B @ k1_xboole_0)) @ 
% 7.03/7.21           (k2_zfmisc_1 @ sk_C_2 @ sk_D)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['51', '56'])).
% 7.03/7.21  thf('58', plain,
% 7.03/7.21      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf('59', plain,
% 7.03/7.21      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 7.03/7.21         ((r2_hidden @ X14 @ X15)
% 7.03/7.21          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X17)))),
% 7.03/7.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 7.03/7.21  thf('60', plain,
% 7.03/7.21      (![X0 : $i, X1 : $i]:
% 7.03/7.21         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 7.03/7.21          | (r2_hidden @ X1 @ sk_A))),
% 7.03/7.21      inference('sup-', [status(thm)], ['58', '59'])).
% 7.03/7.21  thf('61', plain,
% 7.03/7.21      ((((sk_C_2) = (sk_A)) | (r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_A))),
% 7.03/7.21      inference('sup-', [status(thm)], ['57', '60'])).
% 7.03/7.21  thf('62', plain,
% 7.03/7.21      (![X8 : $i, X9 : $i]:
% 7.03/7.21         (((X9) = (X8))
% 7.03/7.21          | ~ (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 7.03/7.21          | ~ (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X9))),
% 7.03/7.21      inference('cnf', [status(esa)], [t2_tarski])).
% 7.03/7.21  thf('63', plain,
% 7.03/7.21      ((((sk_C_2) = (sk_A))
% 7.03/7.21        | ~ (r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2)
% 7.03/7.21        | ((sk_C_2) = (sk_A)))),
% 7.03/7.21      inference('sup-', [status(thm)], ['61', '62'])).
% 7.03/7.21  thf('64', plain,
% 7.03/7.21      ((~ (r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2) | ((sk_C_2) = (sk_A)))),
% 7.03/7.21      inference('simplify', [status(thm)], ['63'])).
% 7.03/7.21  thf('65', plain,
% 7.03/7.21      (((r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2) | ((sk_C_2) = (sk_A)))),
% 7.03/7.21      inference('eq_fact', [status(thm)], ['50'])).
% 7.03/7.21  thf('66', plain, (((sk_C_2) = (sk_A))),
% 7.03/7.21      inference('clc', [status(thm)], ['64', '65'])).
% 7.03/7.21  thf('67', plain,
% 7.03/7.21      (![X0 : $i]:
% 7.03/7.21         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_2 @ sk_D) @ 
% 7.03/7.21             (k2_zfmisc_1 @ sk_C_2 @ X0))
% 7.03/7.21          | (r1_tarski @ sk_B @ X0))),
% 7.03/7.21      inference('demod', [status(thm)], ['37', '66'])).
% 7.03/7.21  thf('68', plain, ((r1_tarski @ sk_B @ sk_D)),
% 7.03/7.21      inference('sup-', [status(thm)], ['32', '67'])).
% 7.03/7.21  thf('69', plain, (((sk_B) = (sk_D))),
% 7.03/7.21      inference('demod', [status(thm)], ['30', '68'])).
% 7.03/7.21  thf('70', plain, ((((sk_A) != (sk_C_2)) | ((sk_B) != (sk_D)))),
% 7.03/7.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.03/7.21  thf('71', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 7.03/7.21      inference('split', [status(esa)], ['70'])).
% 7.03/7.21  thf('72', plain, (((sk_C_2) = (sk_A))),
% 7.03/7.21      inference('clc', [status(thm)], ['64', '65'])).
% 7.03/7.21  thf('73', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 7.03/7.21      inference('split', [status(esa)], ['70'])).
% 7.03/7.21  thf('74', plain, ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 7.03/7.21      inference('sup-', [status(thm)], ['72', '73'])).
% 7.03/7.21  thf('75', plain, ((((sk_A) = (sk_C_2)))),
% 7.03/7.21      inference('simplify', [status(thm)], ['74'])).
% 7.03/7.21  thf('76', plain, (~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C_2)))),
% 7.03/7.21      inference('split', [status(esa)], ['70'])).
% 7.03/7.21  thf('77', plain, (~ (((sk_B) = (sk_D)))),
% 7.03/7.21      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 7.03/7.21  thf('78', plain, (((sk_B) != (sk_D))),
% 7.03/7.21      inference('simpl_trail', [status(thm)], ['71', '77'])).
% 7.03/7.21  thf('79', plain, ($false),
% 7.03/7.21      inference('simplify_reflect-', [status(thm)], ['69', '78'])).
% 7.03/7.21  
% 7.03/7.21  % SZS output end Refutation
% 7.03/7.21  
% 7.03/7.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
