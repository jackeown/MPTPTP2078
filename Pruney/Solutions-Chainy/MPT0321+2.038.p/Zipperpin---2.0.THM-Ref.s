%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QJqA5rMIb5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:37 EST 2020

% Result     : Theorem 47.64s
% Output     : Refutation 47.64s
% Verified   : 
% Statistics : Number of formulae       :  226 (3399 expanded)
%              Number of leaves         :   20 (1000 expanded)
%              Depth                    :   41
%              Number of atoms          : 2032 (35471 expanded)
%              Number of equality atoms :  116 (2318 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X19 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( sk_C @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X18 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

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

thf('29',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( sk_C_1 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ),
    inference(condensation,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('53',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
    | ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 = sk_A ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','69'])).

thf('71',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('74',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X1 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X1 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['82'])).

thf('84',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( r1_tarski @ sk_C_2 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,
    ( ( r1_tarski @ sk_C_2 @ k1_xboole_0 )
    | ( r1_tarski @ sk_D @ sk_B )
    | ( r1_tarski @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tarski @ sk_D @ sk_B )
    | ( r1_tarski @ sk_C_2 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ sk_B )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r1_tarski @ sk_D @ sk_B ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['74','96'])).

thf('98',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ( sk_B = sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('101',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

thf('102',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('103',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ ( k4_xboole_0 @ sk_C_2 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['100','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 ) ),
    inference(condensation,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('110',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_C_2 ) @ sk_C_2 ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('112',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['74','96'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('115',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X2 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X0 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( sk_D
        = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ sk_D @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_D @ sk_B ) @ sk_B )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['111','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_D @ sk_B ) @ sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ( sk_D = sk_B ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_B ) @ sk_B )
    | ( sk_D = sk_B ) ),
    inference(condensation,[status(thm)],['121'])).

thf('123',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['60','61','62'])).

thf('124',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('125',plain,(
    r2_hidden @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_D = sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D @ sk_B ) @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('130',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['134'])).

thf('137',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_C @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['130','139'])).

thf('141',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( sk_C @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('145',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_B ) @ sk_D ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['82'])).

thf('148',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C_1 @ k1_xboole_0 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ k1_xboole_0 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('154',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_A )
    | ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ sk_A )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( r1_tarski @ sk_C_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['145','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X0 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_tarski @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ( sk_C_2
        = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 = sk_A )
      | ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['129','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_A ) @ sk_A )
      | ( r2_hidden @ X0 @ sk_A )
      | ( sk_C_2 = sk_A ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_A ) @ sk_A )
    | ( sk_C_2 = sk_A ) ),
    inference(condensation,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('167',plain,
    ( ( sk_C_2 = sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_2 @ sk_A ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( sk_C_2 = sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_2 @ sk_A ) @ ( sk_C_1 @ k1_xboole_0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('171',plain,
    ( ( sk_C_2 = sk_A )
    | ( r2_hidden @ ( sk_C @ sk_C_2 @ sk_A ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('173',plain,
    ( ( sk_C_2 = sk_A )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['145','159'])).

thf('175',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('176',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
    | ( sk_A = sk_C_2 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    sk_C_2 = sk_A ),
    inference(clc,[status(thm)],['173','176'])).

thf('178',plain,
    ( ( sk_D = sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D @ sk_B ) @ ( sk_C_1 @ sk_C_2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['128','177'])).

thf('179',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['179'])).

thf('181',plain,(
    sk_C_2 = sk_A ),
    inference(clc,[status(thm)],['173','176'])).

thf('182',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['179'])).

thf('183',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    sk_A = sk_C_2 ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['179'])).

thf('186',plain,(
    sk_B != sk_D ),
    inference('sat_resolution*',[status(thm)],['184','185'])).

thf('187',plain,(
    sk_B != sk_D ),
    inference(simpl_trail,[status(thm)],['180','186'])).

thf('188',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_D @ sk_B ) @ ( sk_C_1 @ sk_C_2 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['178','187'])).

thf('189',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('190',plain,(
    r2_hidden @ ( sk_C @ sk_D @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_C_2 ) @ ( sk_C @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['110','192'])).

thf('194',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    sk_C_2 = sk_A ),
    inference(clc,[status(thm)],['173','176'])).

thf('196',plain,
    ( ( k2_zfmisc_1 @ sk_C_2 @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ k1_xboole_0 @ sk_C_2 ) @ ( sk_C @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('199',plain,(
    r2_hidden @ ( sk_C @ sk_D @ sk_B ) @ sk_D ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('201',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['99','201'])).

thf('203',plain,(
    sk_B != sk_D ),
    inference(simpl_trail,[status(thm)],['180','186'])).

thf('204',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['202','203'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QJqA5rMIb5
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:36:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 47.64/47.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 47.64/47.86  % Solved by: fo/fo7.sh
% 47.64/47.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.64/47.86  % done 13475 iterations in 47.403s
% 47.64/47.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 47.64/47.86  % SZS output start Refutation
% 47.64/47.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.64/47.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 47.64/47.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 47.64/47.86  thf(sk_C_2_type, type, sk_C_2: $i).
% 47.64/47.86  thf(sk_D_type, type, sk_D: $i).
% 47.64/47.86  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 47.64/47.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 47.64/47.86  thf(sk_A_type, type, sk_A: $i).
% 47.64/47.86  thf(sk_B_type, type, sk_B: $i).
% 47.64/47.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 47.64/47.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 47.64/47.86  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 47.64/47.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 47.64/47.86  thf(d3_tarski, axiom,
% 47.64/47.86    (![A:$i,B:$i]:
% 47.64/47.86     ( ( r1_tarski @ A @ B ) <=>
% 47.64/47.86       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 47.64/47.86  thf('0', plain,
% 47.64/47.86      (![X1 : $i, X3 : $i]:
% 47.64/47.86         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 47.64/47.86      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.86  thf(t64_zfmisc_1, axiom,
% 47.64/47.86    (![A:$i,B:$i,C:$i]:
% 47.64/47.86     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 47.64/47.86       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 47.64/47.86  thf('1', plain,
% 47.64/47.86      (![X16 : $i, X17 : $i, X19 : $i]:
% 47.64/47.86         ((r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X19)))
% 47.64/47.86          | ((X16) = (X19))
% 47.64/47.86          | ~ (r2_hidden @ X16 @ X17))),
% 47.64/47.86      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 47.64/47.86  thf('2', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.86         ((r1_tarski @ X0 @ X1)
% 47.64/47.86          | ((sk_C @ X1 @ X0) = (X2))
% 47.64/47.86          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 47.64/47.86             (k4_xboole_0 @ X0 @ (k1_tarski @ X2))))),
% 47.64/47.86      inference('sup-', [status(thm)], ['0', '1'])).
% 47.64/47.86  thf('3', plain,
% 47.64/47.86      (![X1 : $i, X3 : $i]:
% 47.64/47.86         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 47.64/47.86      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.86  thf('4', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i]:
% 47.64/47.86         (((sk_C @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1) = (X0))
% 47.64/47.86          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 47.64/47.86          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 47.64/47.86      inference('sup-', [status(thm)], ['2', '3'])).
% 47.64/47.86  thf('5', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i]:
% 47.64/47.86         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 47.64/47.86          | ((sk_C @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1) = (X0)))),
% 47.64/47.86      inference('simplify', [status(thm)], ['4'])).
% 47.64/47.86  thf('6', plain,
% 47.64/47.86      (![X1 : $i, X3 : $i]:
% 47.64/47.86         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 47.64/47.86      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.86  thf('7', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i]:
% 47.64/47.86         ((r2_hidden @ X0 @ X1)
% 47.64/47.86          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 47.64/47.86          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 47.64/47.86      inference('sup+', [status(thm)], ['5', '6'])).
% 47.64/47.86  thf('8', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i]:
% 47.64/47.86         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 47.64/47.86          | (r2_hidden @ X0 @ X1))),
% 47.64/47.86      inference('simplify', [status(thm)], ['7'])).
% 47.64/47.86  thf('9', plain,
% 47.64/47.86      (![X1 : $i, X3 : $i]:
% 47.64/47.86         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 47.64/47.86      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.86  thf('10', plain,
% 47.64/47.86      (![X16 : $i, X17 : $i, X18 : $i]:
% 47.64/47.86         ((r2_hidden @ X16 @ X17)
% 47.64/47.86          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 47.64/47.86      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 47.64/47.86  thf('11', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.86         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 47.64/47.86          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 47.64/47.86             X1))),
% 47.64/47.86      inference('sup-', [status(thm)], ['9', '10'])).
% 47.64/47.86  thf('12', plain,
% 47.64/47.86      (![X1 : $i, X3 : $i]:
% 47.64/47.86         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 47.64/47.86      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.86  thf('13', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i]:
% 47.64/47.86         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 47.64/47.86          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 47.64/47.86      inference('sup-', [status(thm)], ['11', '12'])).
% 47.64/47.86  thf('14', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i]:
% 47.64/47.86         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 47.64/47.86      inference('simplify', [status(thm)], ['13'])).
% 47.64/47.86  thf(d10_xboole_0, axiom,
% 47.64/47.86    (![A:$i,B:$i]:
% 47.64/47.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 47.64/47.86  thf('15', plain,
% 47.64/47.86      (![X6 : $i, X8 : $i]:
% 47.64/47.86         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 47.64/47.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 47.64/47.86  thf('16', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i]:
% 47.64/47.86         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 47.64/47.86          | ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 47.64/47.86      inference('sup-', [status(thm)], ['14', '15'])).
% 47.64/47.86  thf('17', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i]:
% 47.64/47.86         ((r2_hidden @ X0 @ X1)
% 47.64/47.86          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 47.64/47.86      inference('sup-', [status(thm)], ['8', '16'])).
% 47.64/47.86  thf('18', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.86         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 47.64/47.86          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 47.64/47.86             X1))),
% 47.64/47.86      inference('sup-', [status(thm)], ['9', '10'])).
% 47.64/47.86  thf('19', plain,
% 47.64/47.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.86         ((r2_hidden @ (sk_C @ X2 @ X0) @ X0)
% 47.64/47.86          | (r2_hidden @ X1 @ X0)
% 47.64/47.86          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X2))),
% 47.64/47.86      inference('sup+', [status(thm)], ['17', '18'])).
% 47.64/47.86  thf('20', plain,
% 47.64/47.86      (![X1 : $i, X3 : $i]:
% 47.64/47.86         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 47.64/47.86      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.86  thf(t4_boole, axiom,
% 47.64/47.86    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 47.64/47.86  thf('21', plain,
% 47.64/47.86      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 47.64/47.86      inference('cnf', [status(esa)], [t4_boole])).
% 47.64/47.86  thf('22', plain,
% 47.64/47.86      (![X16 : $i, X17 : $i, X18 : $i]:
% 47.64/47.86         (((X16) != (X18))
% 47.64/47.86          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 47.64/47.87      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 47.64/47.87  thf('23', plain,
% 47.64/47.87      (![X17 : $i, X18 : $i]:
% 47.64/47.87         ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18)))),
% 47.64/47.87      inference('simplify', [status(thm)], ['22'])).
% 47.64/47.87  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 47.64/47.87      inference('sup-', [status(thm)], ['21', '23'])).
% 47.64/47.87  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 47.64/47.87      inference('sup-', [status(thm)], ['20', '24'])).
% 47.64/47.87  thf('26', plain,
% 47.64/47.87      (![X6 : $i, X8 : $i]:
% 47.64/47.87         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 47.64/47.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 47.64/47.87  thf('27', plain,
% 47.64/47.87      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['25', '26'])).
% 47.64/47.87  thf('28', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X1)
% 47.64/47.87          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['19', '27'])).
% 47.64/47.87  thf(t134_zfmisc_1, conjecture,
% 47.64/47.87    (![A:$i,B:$i,C:$i,D:$i]:
% 47.64/47.87     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 47.64/47.87       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 47.64/47.87         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 47.64/47.87  thf(zf_stmt_0, negated_conjecture,
% 47.64/47.87    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 47.64/47.87        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 47.64/47.87          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 47.64/47.87            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 47.64/47.87    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 47.64/47.87  thf('29', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf(t2_tarski, axiom,
% 47.64/47.87    (![A:$i,B:$i]:
% 47.64/47.87     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 47.64/47.87       ( ( A ) = ( B ) ) ))).
% 47.64/47.87  thf('30', plain,
% 47.64/47.87      (![X4 : $i, X5 : $i]:
% 47.64/47.87         (((X5) = (X4))
% 47.64/47.87          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 47.64/47.87          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 47.64/47.87      inference('cnf', [status(esa)], [t2_tarski])).
% 47.64/47.87  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 47.64/47.87      inference('sup-', [status(thm)], ['21', '23'])).
% 47.64/47.87  thf('32', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 47.64/47.87          | ((X0) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['30', '31'])).
% 47.64/47.87  thf('33', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 47.64/47.87          | ((X0) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['30', '31'])).
% 47.64/47.87  thf(l54_zfmisc_1, axiom,
% 47.64/47.87    (![A:$i,B:$i,C:$i,D:$i]:
% 47.64/47.87     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 47.64/47.87       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 47.64/47.87  thf('34', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 47.64/47.87         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 47.64/47.87          | ~ (r2_hidden @ X13 @ X15)
% 47.64/47.87          | ~ (r2_hidden @ X11 @ X12))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('35', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         (((X0) = (k1_xboole_0))
% 47.64/47.87          | ~ (r2_hidden @ X2 @ X1)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ k1_xboole_0 @ X0)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X1 @ X0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['33', '34'])).
% 47.64/47.87  thf('36', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (((X0) = (k1_xboole_0))
% 47.64/47.87          | (r2_hidden @ 
% 47.64/47.87             (k4_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 47.64/47.87              (sk_C_1 @ k1_xboole_0 @ X1)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ X1))
% 47.64/47.87          | ((X1) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['32', '35'])).
% 47.64/47.87  thf('37', plain,
% 47.64/47.87      (((r2_hidden @ 
% 47.64/47.87         (k4_tarski @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ 
% 47.64/47.87          (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87         (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 47.64/47.87        | ((sk_B) = (k1_xboole_0))
% 47.64/47.87        | ((sk_A) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup+', [status(thm)], ['29', '36'])).
% 47.64/47.87  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('40', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ 
% 47.64/47.87         (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 47.64/47.87  thf('41', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('42', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X11 @ X12)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('43', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 47.64/47.87          | (r2_hidden @ X1 @ sk_A))),
% 47.64/47.87      inference('sup-', [status(thm)], ['41', '42'])).
% 47.64/47.87  thf('44', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)),
% 47.64/47.87      inference('sup-', [status(thm)], ['40', '43'])).
% 47.64/47.87  thf('45', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 47.64/47.87          | (r2_hidden @ X0 @ X1))),
% 47.64/47.87      inference('simplify', [status(thm)], ['7'])).
% 47.64/47.87  thf('46', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         (~ (r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ X0 @ X2)
% 47.64/47.87          | ~ (r1_tarski @ X1 @ X2))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('47', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 47.64/47.87          | ~ (r2_hidden @ X2 @ X1))),
% 47.64/47.87      inference('sup-', [status(thm)], ['45', '46'])).
% 47.64/47.87  thf('48', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ 
% 47.64/47.87           (k4_xboole_0 @ sk_A @ (k1_tarski @ X0)))
% 47.64/47.87          | (r2_hidden @ X0 @ sk_A))),
% 47.64/47.87      inference('sup-', [status(thm)], ['44', '47'])).
% 47.64/47.87  thf('49', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 47.64/47.87          | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 47.64/47.87          | (r2_hidden @ X0 @ sk_A)
% 47.64/47.87          | (r2_hidden @ X0 @ sk_A))),
% 47.64/47.87      inference('sup+', [status(thm)], ['28', '48'])).
% 47.64/47.87  thf('50', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ sk_A)
% 47.64/47.87          | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 47.64/47.87          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))),
% 47.64/47.87      inference('simplify', [status(thm)], ['49'])).
% 47.64/47.87  thf('51', plain,
% 47.64/47.87      (((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 47.64/47.87        | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 47.64/47.87      inference('condensation', [status(thm)], ['50'])).
% 47.64/47.87  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 47.64/47.87      inference('sup-', [status(thm)], ['21', '23'])).
% 47.64/47.87  thf('53', plain, ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 47.64/47.87      inference('clc', [status(thm)], ['51', '52'])).
% 47.64/47.87  thf('54', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('55', plain,
% 47.64/47.87      (![X4 : $i, X5 : $i]:
% 47.64/47.87         (((X5) = (X4))
% 47.64/47.87          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 47.64/47.87          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 47.64/47.87      inference('cnf', [status(esa)], [t2_tarski])).
% 47.64/47.87  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 47.64/47.87      inference('sup-', [status(thm)], ['21', '23'])).
% 47.64/47.87  thf('57', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 47.64/47.87          | ((k1_xboole_0) = (X0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['55', '56'])).
% 47.64/47.87  thf('58', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         (((X0) = (k1_xboole_0))
% 47.64/47.87          | ~ (r2_hidden @ X2 @ X1)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ k1_xboole_0 @ X0)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X1 @ X0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['33', '34'])).
% 47.64/47.87  thf('59', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (((k1_xboole_0) = (X0))
% 47.64/47.87          | (r2_hidden @ 
% 47.64/47.87             (k4_tarski @ (sk_C_1 @ X0 @ k1_xboole_0) @ 
% 47.64/47.87              (sk_C_1 @ k1_xboole_0 @ X1)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ X1))
% 47.64/47.87          | ((X1) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['57', '58'])).
% 47.64/47.87  thf('60', plain,
% 47.64/47.87      (((r2_hidden @ 
% 47.64/47.87         (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 47.64/47.87          (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87         (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 47.64/47.87        | ((sk_B) = (k1_xboole_0))
% 47.64/47.87        | ((k1_xboole_0) = (sk_A)))),
% 47.64/47.87      inference('sup+', [status(thm)], ['54', '59'])).
% 47.64/47.87  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('62', plain, (((sk_B) != (k1_xboole_0))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('63', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 47.64/47.87         (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('simplify_reflect-', [status(thm)], ['60', '61', '62'])).
% 47.64/47.87  thf('64', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('65', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X13 @ X14)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('66', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 47.64/47.87          | (r2_hidden @ X0 @ sk_B))),
% 47.64/47.87      inference('sup-', [status(thm)], ['64', '65'])).
% 47.64/47.87  thf('67', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_B) @ sk_B)),
% 47.64/47.87      inference('sup-', [status(thm)], ['63', '66'])).
% 47.64/47.87  thf('68', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 47.64/47.87         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 47.64/47.87          | ~ (r2_hidden @ X13 @ X15)
% 47.64/47.87          | ~ (r2_hidden @ X11 @ X12))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('69', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (~ (r2_hidden @ X1 @ X0)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ sk_B)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['67', '68'])).
% 47.64/47.87  thf('70', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 47.64/47.87         (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 47.64/47.87      inference('sup-', [status(thm)], ['53', '69'])).
% 47.64/47.87  thf('71', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('72', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 47.64/47.87         (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('demod', [status(thm)], ['70', '71'])).
% 47.64/47.87  thf('73', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X11 @ X12)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('74', plain, ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_C_2)),
% 47.64/47.87      inference('sup-', [status(thm)], ['72', '73'])).
% 47.64/47.87  thf('75', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 47.64/47.87      inference('sup-', [status(thm)], ['8', '16'])).
% 47.64/47.87  thf('76', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 47.64/47.87          | ((X0) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['30', '31'])).
% 47.64/47.87  thf('77', plain,
% 47.64/47.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 47.64/47.87         ((r2_hidden @ X16 @ X17)
% 47.64/47.87          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 47.64/47.87      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 47.64/47.87  thf('78', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 47.64/47.87          | (r2_hidden @ 
% 47.64/47.87             (sk_C_1 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 47.64/47.87             X1))),
% 47.64/47.87      inference('sup-', [status(thm)], ['76', '77'])).
% 47.64/47.87  thf('79', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 47.64/47.87          | (r2_hidden @ X1 @ X0)
% 47.64/47.87          | ((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup+', [status(thm)], ['75', '78'])).
% 47.64/47.87  thf('80', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 47.64/47.87          | (r2_hidden @ X0 @ X1))),
% 47.64/47.87      inference('simplify', [status(thm)], ['7'])).
% 47.64/47.87  thf('81', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ k1_xboole_0)
% 47.64/47.87          | (r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X1) @ X1)
% 47.64/47.87          | (r2_hidden @ X0 @ X1))),
% 47.64/47.87      inference('sup+', [status(thm)], ['79', '80'])).
% 47.64/47.87  thf('82', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X1) @ X1)
% 47.64/47.87          | (r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r1_tarski @ X1 @ k1_xboole_0))),
% 47.64/47.87      inference('simplify', [status(thm)], ['81'])).
% 47.64/47.87  thf('83', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 47.64/47.87          | (r1_tarski @ X0 @ k1_xboole_0))),
% 47.64/47.87      inference('condensation', [status(thm)], ['82'])).
% 47.64/47.87  thf('84', plain,
% 47.64/47.87      (![X1 : $i, X3 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('85', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 47.64/47.87         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 47.64/47.87          | ~ (r2_hidden @ X13 @ X15)
% 47.64/47.87          | ~ (r2_hidden @ X11 @ X12))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('86', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 47.64/47.87         ((r1_tarski @ X0 @ X1)
% 47.64/47.87          | ~ (r2_hidden @ X3 @ X2)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X2 @ X0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['84', '85'])).
% 47.64/47.87  thf('87', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r1_tarski @ X0 @ k1_xboole_0)
% 47.64/47.87          | (r2_hidden @ 
% 47.64/47.87             (k4_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ (sk_C @ X2 @ X1)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ X1))
% 47.64/47.87          | (r1_tarski @ X1 @ X2))),
% 47.64/47.87      inference('sup-', [status(thm)], ['83', '86'])).
% 47.64/47.87  thf('88', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 47.64/47.87          | (r2_hidden @ X0 @ sk_B))),
% 47.64/47.87      inference('sup-', [status(thm)], ['64', '65'])).
% 47.64/47.87  thf('89', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r1_tarski @ sk_D @ X0)
% 47.64/47.87          | (r1_tarski @ sk_C_2 @ k1_xboole_0)
% 47.64/47.87          | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_B))),
% 47.64/47.87      inference('sup-', [status(thm)], ['87', '88'])).
% 47.64/47.87  thf('90', plain,
% 47.64/47.87      (![X1 : $i, X3 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('91', plain,
% 47.64/47.87      (((r1_tarski @ sk_C_2 @ k1_xboole_0)
% 47.64/47.87        | (r1_tarski @ sk_D @ sk_B)
% 47.64/47.87        | (r1_tarski @ sk_D @ sk_B))),
% 47.64/47.87      inference('sup-', [status(thm)], ['89', '90'])).
% 47.64/47.87  thf('92', plain,
% 47.64/47.87      (((r1_tarski @ sk_D @ sk_B) | (r1_tarski @ sk_C_2 @ k1_xboole_0))),
% 47.64/47.87      inference('simplify', [status(thm)], ['91'])).
% 47.64/47.87  thf('93', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         (~ (r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ X0 @ X2)
% 47.64/47.87          | ~ (r1_tarski @ X1 @ X2))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('94', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r1_tarski @ sk_D @ sk_B)
% 47.64/47.87          | (r2_hidden @ X0 @ k1_xboole_0)
% 47.64/47.87          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 47.64/47.87      inference('sup-', [status(thm)], ['92', '93'])).
% 47.64/47.87  thf('95', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 47.64/47.87      inference('sup-', [status(thm)], ['21', '23'])).
% 47.64/47.87  thf('96', plain,
% 47.64/47.87      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_2) | (r1_tarski @ sk_D @ sk_B))),
% 47.64/47.87      inference('clc', [status(thm)], ['94', '95'])).
% 47.64/47.87  thf('97', plain, ((r1_tarski @ sk_D @ sk_B)),
% 47.64/47.87      inference('sup-', [status(thm)], ['74', '96'])).
% 47.64/47.87  thf('98', plain,
% 47.64/47.87      (![X6 : $i, X8 : $i]:
% 47.64/47.87         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 47.64/47.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 47.64/47.87  thf('99', plain, ((~ (r1_tarski @ sk_B @ sk_D) | ((sk_B) = (sk_D)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['97', '98'])).
% 47.64/47.87  thf('100', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X1)
% 47.64/47.87          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['19', '27'])).
% 47.64/47.87  thf('101', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ 
% 47.64/47.87         (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 47.64/47.87  thf('102', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X11 @ X12)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('103', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_C_2)),
% 47.64/47.87      inference('sup-', [status(thm)], ['101', '102'])).
% 47.64/47.87  thf('104', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 47.64/47.87          | ~ (r2_hidden @ X2 @ X1))),
% 47.64/47.87      inference('sup-', [status(thm)], ['45', '46'])).
% 47.64/47.87  thf('105', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ 
% 47.64/47.87           (k4_xboole_0 @ sk_C_2 @ (k1_tarski @ X0)))
% 47.64/47.87          | (r2_hidden @ X0 @ sk_C_2))),
% 47.64/47.87      inference('sup-', [status(thm)], ['103', '104'])).
% 47.64/47.87  thf('106', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 47.64/47.87          | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_C_2) @ sk_C_2)
% 47.64/47.87          | (r2_hidden @ X0 @ sk_C_2)
% 47.64/47.87          | (r2_hidden @ X0 @ sk_C_2))),
% 47.64/47.87      inference('sup+', [status(thm)], ['100', '105'])).
% 47.64/47.87  thf('107', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ sk_C_2)
% 47.64/47.87          | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_C_2) @ sk_C_2)
% 47.64/47.87          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))),
% 47.64/47.87      inference('simplify', [status(thm)], ['106'])).
% 47.64/47.87  thf('108', plain,
% 47.64/47.87      (((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 47.64/47.87        | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_C_2) @ sk_C_2))),
% 47.64/47.87      inference('condensation', [status(thm)], ['107'])).
% 47.64/47.87  thf('109', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 47.64/47.87      inference('sup-', [status(thm)], ['21', '23'])).
% 47.64/47.87  thf('110', plain, ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_C_2) @ sk_C_2)),
% 47.64/47.87      inference('clc', [status(thm)], ['108', '109'])).
% 47.64/47.87  thf('111', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 47.64/47.87      inference('sup-', [status(thm)], ['8', '16'])).
% 47.64/47.87  thf('112', plain, ((r1_tarski @ sk_D @ sk_B)),
% 47.64/47.87      inference('sup-', [status(thm)], ['74', '96'])).
% 47.64/47.87  thf('113', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 47.64/47.87      inference('sup-', [status(thm)], ['8', '16'])).
% 47.64/47.87  thf('114', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C @ X2 @ X0) @ X0)
% 47.64/47.87          | (r2_hidden @ X1 @ X0)
% 47.64/47.87          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X2))),
% 47.64/47.87      inference('sup+', [status(thm)], ['17', '18'])).
% 47.64/47.87  thf('115', plain,
% 47.64/47.87      (![X6 : $i, X8 : $i]:
% 47.64/47.87         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 47.64/47.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 47.64/47.87  thf('116', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r2_hidden @ X1 @ X2)
% 47.64/47.87          | (r2_hidden @ (sk_C @ X0 @ X2) @ X2)
% 47.64/47.87          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)))
% 47.64/47.87          | ((X0) = (k4_xboole_0 @ X2 @ (k1_tarski @ X1))))),
% 47.64/47.87      inference('sup-', [status(thm)], ['114', '115'])).
% 47.64/47.87  thf('117', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         (~ (r1_tarski @ X2 @ X0)
% 47.64/47.87          | (r2_hidden @ X1 @ X0)
% 47.64/47.87          | ((X2) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 47.64/47.87          | (r2_hidden @ (sk_C @ X2 @ X0) @ X0)
% 47.64/47.87          | (r2_hidden @ X1 @ X0))),
% 47.64/47.87      inference('sup-', [status(thm)], ['113', '116'])).
% 47.64/47.87  thf('118', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C @ X2 @ X0) @ X0)
% 47.64/47.87          | ((X2) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 47.64/47.87          | (r2_hidden @ X1 @ X0)
% 47.64/47.87          | ~ (r1_tarski @ X2 @ X0))),
% 47.64/47.87      inference('simplify', [status(thm)], ['117'])).
% 47.64/47.87  thf('119', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ sk_B)
% 47.64/47.87          | ((sk_D) = (k4_xboole_0 @ sk_B @ (k1_tarski @ X0)))
% 47.64/47.87          | (r2_hidden @ (sk_C @ sk_D @ sk_B) @ sk_B))),
% 47.64/47.87      inference('sup-', [status(thm)], ['112', '118'])).
% 47.64/47.87  thf('120', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         (((sk_D) = (sk_B))
% 47.64/47.87          | (r2_hidden @ X0 @ sk_B)
% 47.64/47.87          | (r2_hidden @ (sk_C @ sk_D @ sk_B) @ sk_B)
% 47.64/47.87          | (r2_hidden @ X0 @ sk_B))),
% 47.64/47.87      inference('sup+', [status(thm)], ['111', '119'])).
% 47.64/47.87  thf('121', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C @ sk_D @ sk_B) @ sk_B)
% 47.64/47.87          | (r2_hidden @ X0 @ sk_B)
% 47.64/47.87          | ((sk_D) = (sk_B)))),
% 47.64/47.87      inference('simplify', [status(thm)], ['120'])).
% 47.64/47.87  thf('122', plain,
% 47.64/47.87      (((r2_hidden @ (sk_C @ sk_D @ sk_B) @ sk_B) | ((sk_D) = (sk_B)))),
% 47.64/47.87      inference('condensation', [status(thm)], ['121'])).
% 47.64/47.87  thf('123', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C_1 @ sk_A @ k1_xboole_0) @ 
% 47.64/47.87         (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('simplify_reflect-', [status(thm)], ['60', '61', '62'])).
% 47.64/47.87  thf('124', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X11 @ X12)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('125', plain, ((r2_hidden @ (sk_C_1 @ sk_A @ k1_xboole_0) @ sk_C_2)),
% 47.64/47.87      inference('sup-', [status(thm)], ['123', '124'])).
% 47.64/47.87  thf('126', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 47.64/47.87         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 47.64/47.87          | ~ (r2_hidden @ X13 @ X15)
% 47.64/47.87          | ~ (r2_hidden @ X11 @ X12))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('127', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (~ (r2_hidden @ X1 @ X0)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_1 @ sk_A @ k1_xboole_0)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ sk_C_2)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['125', '126'])).
% 47.64/47.87  thf('128', plain,
% 47.64/47.87      ((((sk_D) = (sk_B))
% 47.64/47.87        | (r2_hidden @ 
% 47.64/47.87           (k4_tarski @ (sk_C @ sk_D @ sk_B) @ (sk_C_1 @ sk_A @ k1_xboole_0)) @ 
% 47.64/47.87           (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['122', '127'])).
% 47.64/47.87  thf('129', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 47.64/47.87      inference('sup-', [status(thm)], ['8', '16'])).
% 47.64/47.87  thf('130', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('131', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 47.64/47.87      inference('sup-', [status(thm)], ['8', '16'])).
% 47.64/47.87  thf('132', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X1)
% 47.64/47.87          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['19', '27'])).
% 47.64/47.87  thf('133', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (((X0) = (k1_xboole_0))
% 47.64/47.87          | (r2_hidden @ X1 @ X0)
% 47.64/47.87          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 47.64/47.87          | (r2_hidden @ X1 @ X0))),
% 47.64/47.87      inference('sup+', [status(thm)], ['131', '132'])).
% 47.64/47.87  thf('134', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 47.64/47.87          | (r2_hidden @ X1 @ X0)
% 47.64/47.87          | ((X0) = (k1_xboole_0)))),
% 47.64/47.87      inference('simplify', [status(thm)], ['133'])).
% 47.64/47.87  thf('135', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 47.64/47.87      inference('condensation', [status(thm)], ['134'])).
% 47.64/47.87  thf('136', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 47.64/47.87      inference('condensation', [status(thm)], ['134'])).
% 47.64/47.87  thf('137', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 47.64/47.87         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 47.64/47.87          | ~ (r2_hidden @ X13 @ X15)
% 47.64/47.87          | ~ (r2_hidden @ X11 @ X12))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('138', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         (((X0) = (k1_xboole_0))
% 47.64/47.87          | ~ (r2_hidden @ X2 @ X1)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C @ k1_xboole_0 @ X0)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X1 @ X0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['136', '137'])).
% 47.64/47.87  thf('139', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (((X0) = (k1_xboole_0))
% 47.64/47.87          | (r2_hidden @ 
% 47.64/47.87             (k4_tarski @ (sk_C @ k1_xboole_0 @ X0) @ (sk_C @ k1_xboole_0 @ X1)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ X1))
% 47.64/47.87          | ((X1) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['135', '138'])).
% 47.64/47.87  thf('140', plain,
% 47.64/47.87      (((r2_hidden @ 
% 47.64/47.87         (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ (sk_C @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87         (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 47.64/47.87        | ((sk_B) = (k1_xboole_0))
% 47.64/47.87        | ((sk_A) = (k1_xboole_0)))),
% 47.64/47.87      inference('sup+', [status(thm)], ['130', '139'])).
% 47.64/47.87  thf('141', plain, (((sk_A) != (k1_xboole_0))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('142', plain, (((sk_B) != (k1_xboole_0))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('143', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_A) @ (sk_C @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('simplify_reflect-', [status(thm)], ['140', '141', '142'])).
% 47.64/47.87  thf('144', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X13 @ X14)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('145', plain, ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_B) @ sk_D)),
% 47.64/47.87      inference('sup-', [status(thm)], ['143', '144'])).
% 47.64/47.87  thf('146', plain,
% 47.64/47.87      (![X1 : $i, X3 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('147', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 47.64/47.87          | (r1_tarski @ X0 @ k1_xboole_0))),
% 47.64/47.87      inference('condensation', [status(thm)], ['82'])).
% 47.64/47.87  thf('148', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 47.64/47.87         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 47.64/47.87          | ~ (r2_hidden @ X13 @ X15)
% 47.64/47.87          | ~ (r2_hidden @ X11 @ X12))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('149', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r1_tarski @ X0 @ k1_xboole_0)
% 47.64/47.87          | ~ (r2_hidden @ X2 @ X1)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_1 @ k1_xboole_0 @ X0)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X1 @ X0)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['147', '148'])).
% 47.64/47.87  thf('150', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r1_tarski @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ 
% 47.64/47.87             (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C_1 @ k1_xboole_0 @ X2)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ X2))
% 47.64/47.87          | (r1_tarski @ X2 @ k1_xboole_0))),
% 47.64/47.87      inference('sup-', [status(thm)], ['146', '149'])).
% 47.64/47.87  thf('151', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 47.64/47.87          | (r2_hidden @ X1 @ sk_A))),
% 47.64/47.87      inference('sup-', [status(thm)], ['41', '42'])).
% 47.64/47.87  thf('152', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r1_tarski @ sk_D @ k1_xboole_0)
% 47.64/47.87          | (r1_tarski @ sk_C_2 @ X0)
% 47.64/47.87          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 47.64/47.87      inference('sup-', [status(thm)], ['150', '151'])).
% 47.64/47.87  thf('153', plain,
% 47.64/47.87      (![X1 : $i, X3 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('154', plain,
% 47.64/47.87      (((r1_tarski @ sk_C_2 @ sk_A)
% 47.64/47.87        | (r1_tarski @ sk_D @ k1_xboole_0)
% 47.64/47.87        | (r1_tarski @ sk_C_2 @ sk_A))),
% 47.64/47.87      inference('sup-', [status(thm)], ['152', '153'])).
% 47.64/47.87  thf('155', plain,
% 47.64/47.87      (((r1_tarski @ sk_D @ k1_xboole_0) | (r1_tarski @ sk_C_2 @ sk_A))),
% 47.64/47.87      inference('simplify', [status(thm)], ['154'])).
% 47.64/47.87  thf('156', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         (~ (r2_hidden @ X0 @ X1)
% 47.64/47.87          | (r2_hidden @ X0 @ X2)
% 47.64/47.87          | ~ (r1_tarski @ X1 @ X2))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('157', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r1_tarski @ sk_C_2 @ sk_A)
% 47.64/47.87          | (r2_hidden @ X0 @ k1_xboole_0)
% 47.64/47.87          | ~ (r2_hidden @ X0 @ sk_D))),
% 47.64/47.87      inference('sup-', [status(thm)], ['155', '156'])).
% 47.64/47.87  thf('158', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 47.64/47.87      inference('sup-', [status(thm)], ['21', '23'])).
% 47.64/47.87  thf('159', plain,
% 47.64/47.87      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_D) | (r1_tarski @ sk_C_2 @ sk_A))),
% 47.64/47.87      inference('clc', [status(thm)], ['157', '158'])).
% 47.64/47.87  thf('160', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 47.64/47.87      inference('sup-', [status(thm)], ['145', '159'])).
% 47.64/47.87  thf('161', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C @ X2 @ X0) @ X0)
% 47.64/47.87          | ((X2) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 47.64/47.87          | (r2_hidden @ X1 @ X0)
% 47.64/47.87          | ~ (r1_tarski @ X2 @ X0))),
% 47.64/47.87      inference('simplify', [status(thm)], ['117'])).
% 47.64/47.87  thf('162', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ X0 @ sk_A)
% 47.64/47.87          | ((sk_C_2) = (k4_xboole_0 @ sk_A @ (k1_tarski @ X0)))
% 47.64/47.87          | (r2_hidden @ (sk_C @ sk_C_2 @ sk_A) @ sk_A))),
% 47.64/47.87      inference('sup-', [status(thm)], ['160', '161'])).
% 47.64/47.87  thf('163', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         (((sk_C_2) = (sk_A))
% 47.64/47.87          | (r2_hidden @ X0 @ sk_A)
% 47.64/47.87          | (r2_hidden @ (sk_C @ sk_C_2 @ sk_A) @ sk_A)
% 47.64/47.87          | (r2_hidden @ X0 @ sk_A))),
% 47.64/47.87      inference('sup+', [status(thm)], ['129', '162'])).
% 47.64/47.87  thf('164', plain,
% 47.64/47.87      (![X0 : $i]:
% 47.64/47.87         ((r2_hidden @ (sk_C @ sk_C_2 @ sk_A) @ sk_A)
% 47.64/47.87          | (r2_hidden @ X0 @ sk_A)
% 47.64/47.87          | ((sk_C_2) = (sk_A)))),
% 47.64/47.87      inference('simplify', [status(thm)], ['163'])).
% 47.64/47.87  thf('165', plain,
% 47.64/47.87      (((r2_hidden @ (sk_C @ sk_C_2 @ sk_A) @ sk_A) | ((sk_C_2) = (sk_A)))),
% 47.64/47.87      inference('condensation', [status(thm)], ['164'])).
% 47.64/47.87  thf('166', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (~ (r2_hidden @ X1 @ X0)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ sk_B)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['67', '68'])).
% 47.64/47.87  thf('167', plain,
% 47.64/47.87      ((((sk_C_2) = (sk_A))
% 47.64/47.87        | (r2_hidden @ 
% 47.64/47.87           (k4_tarski @ (sk_C @ sk_C_2 @ sk_A) @ (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['165', '166'])).
% 47.64/47.87  thf('168', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('169', plain,
% 47.64/47.87      ((((sk_C_2) = (sk_A))
% 47.64/47.87        | (r2_hidden @ 
% 47.64/47.87           (k4_tarski @ (sk_C @ sk_C_2 @ sk_A) @ (sk_C_1 @ k1_xboole_0 @ sk_B)) @ 
% 47.64/47.87           (k2_zfmisc_1 @ sk_C_2 @ sk_D)))),
% 47.64/47.87      inference('demod', [status(thm)], ['167', '168'])).
% 47.64/47.87  thf('170', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X11 @ X12)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('171', plain,
% 47.64/47.87      ((((sk_C_2) = (sk_A)) | (r2_hidden @ (sk_C @ sk_C_2 @ sk_A) @ sk_C_2))),
% 47.64/47.87      inference('sup-', [status(thm)], ['169', '170'])).
% 47.64/47.87  thf('172', plain,
% 47.64/47.87      (![X1 : $i, X3 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('173', plain, ((((sk_C_2) = (sk_A)) | (r1_tarski @ sk_A @ sk_C_2))),
% 47.64/47.87      inference('sup-', [status(thm)], ['171', '172'])).
% 47.64/47.87  thf('174', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 47.64/47.87      inference('sup-', [status(thm)], ['145', '159'])).
% 47.64/47.87  thf('175', plain,
% 47.64/47.87      (![X6 : $i, X8 : $i]:
% 47.64/47.87         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 47.64/47.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 47.64/47.87  thf('176', plain, ((~ (r1_tarski @ sk_A @ sk_C_2) | ((sk_A) = (sk_C_2)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['174', '175'])).
% 47.64/47.87  thf('177', plain, (((sk_C_2) = (sk_A))),
% 47.64/47.87      inference('clc', [status(thm)], ['173', '176'])).
% 47.64/47.87  thf('178', plain,
% 47.64/47.87      ((((sk_D) = (sk_B))
% 47.64/47.87        | (r2_hidden @ 
% 47.64/47.87           (k4_tarski @ (sk_C @ sk_D @ sk_B) @ (sk_C_1 @ sk_C_2 @ k1_xboole_0)) @ 
% 47.64/47.87           (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 47.64/47.87      inference('demod', [status(thm)], ['128', '177'])).
% 47.64/47.87  thf('179', plain, ((((sk_A) != (sk_C_2)) | ((sk_B) != (sk_D)))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('180', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 47.64/47.87      inference('split', [status(esa)], ['179'])).
% 47.64/47.87  thf('181', plain, (((sk_C_2) = (sk_A))),
% 47.64/47.87      inference('clc', [status(thm)], ['173', '176'])).
% 47.64/47.87  thf('182', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 47.64/47.87      inference('split', [status(esa)], ['179'])).
% 47.64/47.87  thf('183', plain, ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 47.64/47.87      inference('sup-', [status(thm)], ['181', '182'])).
% 47.64/47.87  thf('184', plain, ((((sk_A) = (sk_C_2)))),
% 47.64/47.87      inference('simplify', [status(thm)], ['183'])).
% 47.64/47.87  thf('185', plain, (~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C_2)))),
% 47.64/47.87      inference('split', [status(esa)], ['179'])).
% 47.64/47.87  thf('186', plain, (~ (((sk_B) = (sk_D)))),
% 47.64/47.87      inference('sat_resolution*', [status(thm)], ['184', '185'])).
% 47.64/47.87  thf('187', plain, (((sk_B) != (sk_D))),
% 47.64/47.87      inference('simpl_trail', [status(thm)], ['180', '186'])).
% 47.64/47.87  thf('188', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C @ sk_D @ sk_B) @ (sk_C_1 @ sk_C_2 @ k1_xboole_0)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_B @ sk_C_2))),
% 47.64/47.87      inference('simplify_reflect-', [status(thm)], ['178', '187'])).
% 47.64/47.87  thf('189', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X11 @ X12)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('190', plain, ((r2_hidden @ (sk_C @ sk_D @ sk_B) @ sk_B)),
% 47.64/47.87      inference('sup-', [status(thm)], ['188', '189'])).
% 47.64/47.87  thf('191', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 47.64/47.87         ((r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X15))
% 47.64/47.87          | ~ (r2_hidden @ X13 @ X15)
% 47.64/47.87          | ~ (r2_hidden @ X11 @ X12))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('192', plain,
% 47.64/47.87      (![X0 : $i, X1 : $i]:
% 47.64/47.87         (~ (r2_hidden @ X1 @ X0)
% 47.64/47.87          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C @ sk_D @ sk_B)) @ 
% 47.64/47.87             (k2_zfmisc_1 @ X0 @ sk_B)))),
% 47.64/47.87      inference('sup-', [status(thm)], ['190', '191'])).
% 47.64/47.87  thf('193', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_C_2) @ (sk_C @ sk_D @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_C_2 @ sk_B))),
% 47.64/47.87      inference('sup-', [status(thm)], ['110', '192'])).
% 47.64/47.87  thf('194', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.64/47.87  thf('195', plain, (((sk_C_2) = (sk_A))),
% 47.64/47.87      inference('clc', [status(thm)], ['173', '176'])).
% 47.64/47.87  thf('196', plain,
% 47.64/47.87      (((k2_zfmisc_1 @ sk_C_2 @ sk_B) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('demod', [status(thm)], ['194', '195'])).
% 47.64/47.87  thf('197', plain,
% 47.64/47.87      ((r2_hidden @ 
% 47.64/47.87        (k4_tarski @ (sk_C @ k1_xboole_0 @ sk_C_2) @ (sk_C @ sk_D @ sk_B)) @ 
% 47.64/47.87        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 47.64/47.87      inference('demod', [status(thm)], ['193', '196'])).
% 47.64/47.87  thf('198', plain,
% 47.64/47.87      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 47.64/47.87         ((r2_hidden @ X13 @ X14)
% 47.64/47.87          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 47.64/47.87      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.64/47.87  thf('199', plain, ((r2_hidden @ (sk_C @ sk_D @ sk_B) @ sk_D)),
% 47.64/47.87      inference('sup-', [status(thm)], ['197', '198'])).
% 47.64/47.87  thf('200', plain,
% 47.64/47.87      (![X1 : $i, X3 : $i]:
% 47.64/47.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 47.64/47.87      inference('cnf', [status(esa)], [d3_tarski])).
% 47.64/47.87  thf('201', plain, ((r1_tarski @ sk_B @ sk_D)),
% 47.64/47.87      inference('sup-', [status(thm)], ['199', '200'])).
% 47.64/47.87  thf('202', plain, (((sk_B) = (sk_D))),
% 47.64/47.87      inference('demod', [status(thm)], ['99', '201'])).
% 47.64/47.87  thf('203', plain, (((sk_B) != (sk_D))),
% 47.64/47.87      inference('simpl_trail', [status(thm)], ['180', '186'])).
% 47.64/47.87  thf('204', plain, ($false),
% 47.64/47.87      inference('simplify_reflect-', [status(thm)], ['202', '203'])).
% 47.64/47.87  
% 47.64/47.87  % SZS output end Refutation
% 47.64/47.87  
% 47.64/47.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
