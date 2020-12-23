%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KysIErKqMX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:38 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 350 expanded)
%              Number of leaves         :   19 ( 113 expanded)
%              Depth                    :   19
%              Number of atoms          :  830 (3595 expanded)
%              Number of equality atoms :   79 ( 427 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_A )
    | ( sk_D = k1_xboole_0 )
    | ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('13',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C_2 = sk_A )
    | ( r2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('15',plain,
    ( ( sk_C_2 = sk_A )
    | ( sk_D = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ sk_C_2 )
    | ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C_2 = sk_A )
    | ( r2_hidden @ ( sk_C_1 @ sk_A @ sk_C_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('30',plain,
    ( ( sk_C_2 = sk_A )
    | ( sk_D = k1_xboole_0 )
    | ~ ( r2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C_2 = sk_A )
    | ( r2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('32',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_C_2 = sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B_1 != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_A != sk_C_2 )
   <= ( sk_A != sk_C_2 ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A != sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A != sk_C_2 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,
    ( ( r1_tarski @ sk_D @ sk_B_1 )
    | ( r1_tarski @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ sk_D @ sk_B_1 ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('60',plain,
    ( ( sk_D = sk_B_1 )
    | ( r2_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('62',plain,
    ( ( sk_D = sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_D ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_D ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ sk_B_1 @ sk_D ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_D = sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['62','76'])).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_xboole_0 @ X7 @ X8 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('79',plain,
    ( ( sk_D = sk_B_1 )
    | ~ ( r2_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_D = sk_B_1 )
    | ( r2_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('81',plain,(
    sk_D = sk_B_1 ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','81'])).

thf('83',plain,
    ( $false
   <= ( sk_A != sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['36','82'])).

thf('84',plain,(
    sk_D = sk_B_1 ),
    inference(clc,[status(thm)],['79','80'])).

thf('85',plain,
    ( ( sk_B_1 != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['33'])).

thf('86',plain,
    ( ( sk_D != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_B_1 = sk_D ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_A != sk_C_2 )
    | ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['33'])).

thf('89',plain,(
    sk_A != sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['83','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KysIErKqMX
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:22:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.77/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.94  % Solved by: fo/fo7.sh
% 0.77/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.94  % done 389 iterations in 0.490s
% 0.77/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.94  % SZS output start Refutation
% 0.77/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.94  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.77/0.94  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.77/0.94  thf(sk_B_type, type, sk_B: $i > $i).
% 0.77/0.94  thf(sk_D_type, type, sk_D: $i).
% 0.77/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.94  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.77/0.94  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.77/0.94  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.77/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.94  thf(d3_tarski, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ( r1_tarski @ A @ B ) <=>
% 0.77/0.94       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/0.94  thf('0', plain,
% 0.77/0.94      (![X1 : $i, X3 : $i]:
% 0.77/0.94         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.94  thf(t7_xboole_0, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.77/0.94          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.77/0.94  thf('1', plain,
% 0.77/0.94      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.77/0.94      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/0.94  thf(l54_zfmisc_1, axiom,
% 0.77/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.94     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.77/0.94       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.77/0.94  thf('2', plain,
% 0.77/0.94      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.77/0.94         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.77/0.94          | ~ (r2_hidden @ X12 @ X14)
% 0.77/0.94          | ~ (r2_hidden @ X10 @ X11))),
% 0.77/0.94      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.77/0.94  thf('3', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.94         (((X0) = (k1_xboole_0))
% 0.77/0.94          | ~ (r2_hidden @ X2 @ X1)
% 0.77/0.94          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.77/0.94             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('4', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.94         ((r1_tarski @ X0 @ X1)
% 0.77/0.94          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.77/0.94             (k2_zfmisc_1 @ X0 @ X2))
% 0.77/0.94          | ((X2) = (k1_xboole_0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['0', '3'])).
% 0.77/0.94  thf(t134_zfmisc_1, conjecture,
% 0.77/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.94     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.77/0.94       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/0.94         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.77/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.94    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.94        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.77/0.94          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/0.94            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 0.77/0.94    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 0.77/0.94  thf('5', plain,
% 0.77/0.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('6', plain,
% 0.77/0.94      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.94         ((r2_hidden @ X10 @ X11)
% 0.77/0.94          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.77/0.94      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.77/0.94  thf('7', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.77/0.94          | (r2_hidden @ X1 @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['5', '6'])).
% 0.77/0.94  thf('8', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (((sk_D) = (k1_xboole_0))
% 0.77/0.94          | (r1_tarski @ sk_C_2 @ X0)
% 0.77/0.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['4', '7'])).
% 0.77/0.94  thf('9', plain,
% 0.77/0.94      (![X1 : $i, X3 : $i]:
% 0.77/0.94         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.94  thf('10', plain,
% 0.77/0.94      (((r1_tarski @ sk_C_2 @ sk_A)
% 0.77/0.94        | ((sk_D) = (k1_xboole_0))
% 0.77/0.94        | (r1_tarski @ sk_C_2 @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['8', '9'])).
% 0.77/0.94  thf('11', plain, ((((sk_D) = (k1_xboole_0)) | (r1_tarski @ sk_C_2 @ sk_A))),
% 0.77/0.94      inference('simplify', [status(thm)], ['10'])).
% 0.77/0.94  thf(d8_xboole_0, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.77/0.94       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.77/0.94  thf('12', plain,
% 0.77/0.94      (![X4 : $i, X6 : $i]:
% 0.77/0.94         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.77/0.94      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.77/0.94  thf('13', plain,
% 0.77/0.94      ((((sk_D) = (k1_xboole_0))
% 0.77/0.94        | ((sk_C_2) = (sk_A))
% 0.77/0.94        | (r2_xboole_0 @ sk_C_2 @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['11', '12'])).
% 0.77/0.94  thf(t6_xboole_0, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.77/0.94          ( ![C:$i]:
% 0.77/0.94            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.77/0.94  thf('14', plain,
% 0.77/0.94      (![X7 : $i, X8 : $i]:
% 0.77/0.94         (~ (r2_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 0.77/0.94      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.77/0.94  thf('15', plain,
% 0.77/0.94      ((((sk_C_2) = (sk_A))
% 0.77/0.94        | ((sk_D) = (k1_xboole_0))
% 0.77/0.94        | (r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.94  thf('16', plain,
% 0.77/0.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('17', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.94         ((r1_tarski @ X0 @ X1)
% 0.77/0.94          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.77/0.94             (k2_zfmisc_1 @ X0 @ X2))
% 0.77/0.94          | ((X2) = (k1_xboole_0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['0', '3'])).
% 0.77/0.94  thf('18', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.77/0.94           (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.77/0.94          | ((sk_B_1) = (k1_xboole_0))
% 0.77/0.94          | (r1_tarski @ sk_A @ X0))),
% 0.77/0.94      inference('sup+', [status(thm)], ['16', '17'])).
% 0.77/0.94  thf('19', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('20', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.77/0.94           (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.77/0.94          | (r1_tarski @ sk_A @ X0))),
% 0.77/0.94      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.77/0.94  thf('21', plain,
% 0.77/0.94      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.94         ((r2_hidden @ X10 @ X11)
% 0.77/0.94          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.77/0.94      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.77/0.94  thf('22', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_2))),
% 0.77/0.94      inference('sup-', [status(thm)], ['20', '21'])).
% 0.77/0.94  thf('23', plain,
% 0.77/0.94      (![X1 : $i, X3 : $i]:
% 0.77/0.94         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.94  thf('24', plain,
% 0.77/0.94      (((r1_tarski @ sk_A @ sk_C_2) | (r1_tarski @ sk_A @ sk_C_2))),
% 0.77/0.94      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/0.94  thf('25', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 0.77/0.94      inference('simplify', [status(thm)], ['24'])).
% 0.77/0.94  thf('26', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.94         (~ (r2_hidden @ X0 @ X1)
% 0.77/0.94          | (r2_hidden @ X0 @ X2)
% 0.77/0.94          | ~ (r1_tarski @ X1 @ X2))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.94  thf('27', plain,
% 0.77/0.94      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['25', '26'])).
% 0.77/0.94  thf('28', plain,
% 0.77/0.94      ((((sk_D) = (k1_xboole_0))
% 0.77/0.94        | ((sk_C_2) = (sk_A))
% 0.77/0.94        | (r2_hidden @ (sk_C_1 @ sk_A @ sk_C_2) @ sk_C_2))),
% 0.77/0.94      inference('sup-', [status(thm)], ['15', '27'])).
% 0.77/0.94  thf('29', plain,
% 0.77/0.94      (![X7 : $i, X8 : $i]:
% 0.77/0.94         (~ (r2_xboole_0 @ X7 @ X8) | ~ (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 0.77/0.94      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.77/0.94  thf('30', plain,
% 0.77/0.94      ((((sk_C_2) = (sk_A))
% 0.77/0.94        | ((sk_D) = (k1_xboole_0))
% 0.77/0.94        | ~ (r2_xboole_0 @ sk_C_2 @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.94  thf('31', plain,
% 0.77/0.94      ((((sk_D) = (k1_xboole_0))
% 0.77/0.94        | ((sk_C_2) = (sk_A))
% 0.77/0.94        | (r2_xboole_0 @ sk_C_2 @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['11', '12'])).
% 0.77/0.94  thf('32', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_C_2) = (sk_A)))),
% 0.77/0.94      inference('clc', [status(thm)], ['30', '31'])).
% 0.77/0.94  thf('33', plain, ((((sk_A) != (sk_C_2)) | ((sk_B_1) != (sk_D)))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('34', plain, ((((sk_A) != (sk_C_2))) <= (~ (((sk_A) = (sk_C_2))))),
% 0.77/0.94      inference('split', [status(esa)], ['33'])).
% 0.77/0.94  thf('35', plain,
% 0.77/0.94      (((((sk_C_2) != (sk_C_2)) | ((sk_D) = (k1_xboole_0))))
% 0.77/0.94         <= (~ (((sk_A) = (sk_C_2))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['32', '34'])).
% 0.77/0.94  thf('36', plain, ((((sk_D) = (k1_xboole_0))) <= (~ (((sk_A) = (sk_C_2))))),
% 0.77/0.94      inference('simplify', [status(thm)], ['35'])).
% 0.77/0.94  thf('37', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('38', plain,
% 0.77/0.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('39', plain,
% 0.77/0.94      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.77/0.94      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/0.94  thf('40', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.94         (((X0) = (k1_xboole_0))
% 0.77/0.94          | ~ (r2_hidden @ X2 @ X1)
% 0.77/0.94          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.77/0.94             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('41', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         (((X0) = (k1_xboole_0))
% 0.77/0.94          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.77/0.94             (k2_zfmisc_1 @ X0 @ X1))
% 0.77/0.94          | ((X1) = (k1_xboole_0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/0.94  thf('42', plain,
% 0.77/0.94      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.77/0.94         (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.77/0.94        | ((sk_B_1) = (k1_xboole_0))
% 0.77/0.94        | ((sk_A) = (k1_xboole_0)))),
% 0.77/0.94      inference('sup+', [status(thm)], ['38', '41'])).
% 0.77/0.94  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('44', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('45', plain,
% 0.77/0.94      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.77/0.94        (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 0.77/0.94      inference('simplify_reflect-', [status(thm)], ['42', '43', '44'])).
% 0.77/0.94  thf('46', plain,
% 0.77/0.94      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.94         ((r2_hidden @ X10 @ X11)
% 0.77/0.94          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.77/0.94      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.77/0.94  thf('47', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_C_2)),
% 0.77/0.94      inference('sup-', [status(thm)], ['45', '46'])).
% 0.77/0.94  thf('48', plain,
% 0.77/0.94      (![X1 : $i, X3 : $i]:
% 0.77/0.94         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.94  thf('49', plain,
% 0.77/0.94      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.77/0.94         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.77/0.94          | ~ (r2_hidden @ X12 @ X14)
% 0.77/0.94          | ~ (r2_hidden @ X10 @ X11))),
% 0.77/0.94      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.77/0.94  thf('50', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.94         ((r1_tarski @ X0 @ X1)
% 0.77/0.94          | ~ (r2_hidden @ X3 @ X2)
% 0.77/0.94          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.77/0.94             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/0.94  thf('51', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X1 @ X0)) @ 
% 0.77/0.94           (k2_zfmisc_1 @ sk_C_2 @ X0))
% 0.77/0.94          | (r1_tarski @ X0 @ X1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['47', '50'])).
% 0.77/0.94  thf('52', plain,
% 0.77/0.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('53', plain,
% 0.77/0.94      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.94         ((r2_hidden @ X12 @ X13)
% 0.77/0.94          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.77/0.94      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.77/0.94  thf('54', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.77/0.94          | (r2_hidden @ X0 @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['52', '53'])).
% 0.77/0.94  thf('55', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((r1_tarski @ sk_D @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['51', '54'])).
% 0.77/0.94  thf('56', plain,
% 0.77/0.94      (![X1 : $i, X3 : $i]:
% 0.77/0.94         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.94  thf('57', plain,
% 0.77/0.94      (((r1_tarski @ sk_D @ sk_B_1) | (r1_tarski @ sk_D @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['55', '56'])).
% 0.77/0.94  thf('58', plain, ((r1_tarski @ sk_D @ sk_B_1)),
% 0.77/0.94      inference('simplify', [status(thm)], ['57'])).
% 0.77/0.94  thf('59', plain,
% 0.77/0.94      (![X4 : $i, X6 : $i]:
% 0.77/0.94         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.77/0.94      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.77/0.94  thf('60', plain, ((((sk_D) = (sk_B_1)) | (r2_xboole_0 @ sk_D @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['58', '59'])).
% 0.77/0.94  thf('61', plain,
% 0.77/0.94      (![X7 : $i, X8 : $i]:
% 0.77/0.94         (~ (r2_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X8))),
% 0.77/0.94      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.77/0.94  thf('62', plain,
% 0.77/0.94      ((((sk_D) = (sk_B_1)) | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_D) @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['60', '61'])).
% 0.77/0.94  thf('63', plain,
% 0.77/0.94      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_2 @ sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('64', plain,
% 0.77/0.94      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.77/0.94      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.77/0.94  thf('65', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.94         ((r1_tarski @ X0 @ X1)
% 0.77/0.94          | ~ (r2_hidden @ X3 @ X2)
% 0.77/0.94          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.77/0.94             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/0.94  thf('66', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.94         (((X0) = (k1_xboole_0))
% 0.77/0.94          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.77/0.94             (k2_zfmisc_1 @ X0 @ X1))
% 0.77/0.94          | (r1_tarski @ X1 @ X2))),
% 0.77/0.94      inference('sup-', [status(thm)], ['64', '65'])).
% 0.77/0.94  thf('67', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.77/0.94           (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.77/0.94          | (r1_tarski @ sk_B_1 @ X0)
% 0.77/0.94          | ((sk_A) = (k1_xboole_0)))),
% 0.77/0.94      inference('sup+', [status(thm)], ['63', '66'])).
% 0.77/0.94  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('69', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.77/0.94           (k2_zfmisc_1 @ sk_C_2 @ sk_D))
% 0.77/0.94          | (r1_tarski @ sk_B_1 @ X0))),
% 0.77/0.94      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.77/0.94  thf('70', plain,
% 0.77/0.94      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.94         ((r2_hidden @ X12 @ X13)
% 0.77/0.94          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.77/0.94      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.77/0.94  thf('71', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_D))),
% 0.77/0.94      inference('sup-', [status(thm)], ['69', '70'])).
% 0.77/0.94  thf('72', plain,
% 0.77/0.94      (![X1 : $i, X3 : $i]:
% 0.77/0.94         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.94  thf('73', plain,
% 0.77/0.94      (((r1_tarski @ sk_B_1 @ sk_D) | (r1_tarski @ sk_B_1 @ sk_D))),
% 0.77/0.94      inference('sup-', [status(thm)], ['71', '72'])).
% 0.77/0.94  thf('74', plain, ((r1_tarski @ sk_B_1 @ sk_D)),
% 0.77/0.94      inference('simplify', [status(thm)], ['73'])).
% 0.77/0.94  thf('75', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.94         (~ (r2_hidden @ X0 @ X1)
% 0.77/0.94          | (r2_hidden @ X0 @ X2)
% 0.77/0.94          | ~ (r1_tarski @ X1 @ X2))),
% 0.77/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.94  thf('76', plain,
% 0.77/0.94      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['74', '75'])).
% 0.77/0.94  thf('77', plain,
% 0.77/0.94      ((((sk_D) = (sk_B_1)) | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_D) @ sk_D))),
% 0.77/0.94      inference('sup-', [status(thm)], ['62', '76'])).
% 0.77/0.94  thf('78', plain,
% 0.77/0.94      (![X7 : $i, X8 : $i]:
% 0.77/0.94         (~ (r2_xboole_0 @ X7 @ X8) | ~ (r2_hidden @ (sk_C_1 @ X8 @ X7) @ X7))),
% 0.77/0.94      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.77/0.94  thf('79', plain, ((((sk_D) = (sk_B_1)) | ~ (r2_xboole_0 @ sk_D @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['77', '78'])).
% 0.77/0.94  thf('80', plain, ((((sk_D) = (sk_B_1)) | (r2_xboole_0 @ sk_D @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['58', '59'])).
% 0.77/0.94  thf('81', plain, (((sk_D) = (sk_B_1))),
% 0.77/0.94      inference('clc', [status(thm)], ['79', '80'])).
% 0.77/0.94  thf('82', plain, (((sk_D) != (k1_xboole_0))),
% 0.77/0.94      inference('demod', [status(thm)], ['37', '81'])).
% 0.77/0.94  thf('83', plain, (($false) <= (~ (((sk_A) = (sk_C_2))))),
% 0.77/0.94      inference('simplify_reflect-', [status(thm)], ['36', '82'])).
% 0.77/0.94  thf('84', plain, (((sk_D) = (sk_B_1))),
% 0.77/0.94      inference('clc', [status(thm)], ['79', '80'])).
% 0.77/0.94  thf('85', plain, ((((sk_B_1) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 0.77/0.94      inference('split', [status(esa)], ['33'])).
% 0.77/0.94  thf('86', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['84', '85'])).
% 0.77/0.94  thf('87', plain, ((((sk_B_1) = (sk_D)))),
% 0.77/0.94      inference('simplify', [status(thm)], ['86'])).
% 0.77/0.94  thf('88', plain, (~ (((sk_A) = (sk_C_2))) | ~ (((sk_B_1) = (sk_D)))),
% 0.77/0.94      inference('split', [status(esa)], ['33'])).
% 0.77/0.94  thf('89', plain, (~ (((sk_A) = (sk_C_2)))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.77/0.94  thf('90', plain, ($false),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['83', '89'])).
% 0.77/0.94  
% 0.77/0.94  % SZS output end Refutation
% 0.77/0.94  
% 0.77/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
