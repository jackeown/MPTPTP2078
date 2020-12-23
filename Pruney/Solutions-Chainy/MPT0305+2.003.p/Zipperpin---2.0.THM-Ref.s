%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ez79kWDigt

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:11 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 237 expanded)
%              Number of leaves         :   18 (  77 expanded)
%              Depth                    :   22
%              Number of atoms          :  800 (2503 expanded)
%              Number of equality atoms :    8 (  52 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t117_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
          & ~ ( r1_tarski @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t117_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X13 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X13 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('32',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('39',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['19','20'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_B @ sk_A ) @ sk_A )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X13 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
        | ( r1_tarski @ X0 @ X1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_2 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
      | ( r1_tarski @ sk_B_1 @ sk_C_2 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('58',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['32','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('62',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ez79kWDigt
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 578 iterations in 0.630s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.08  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.08  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.90/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.08  thf(t117_zfmisc_1, conjecture,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.90/1.08          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.90/1.08            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.90/1.08          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.08        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.90/1.08             ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.90/1.08               ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.90/1.08             ( ~( r1_tarski @ B @ C ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t117_zfmisc_1])).
% 0.90/1.08  thf('0', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(d3_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      (![X4 : $i, X6 : $i]:
% 0.90/1.08         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf(d1_xboole_0, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.90/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.90/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.08  thf(l54_zfmisc_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.08     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.90/1.08       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.90/1.08         ((r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X13))
% 0.90/1.08          | ~ (r2_hidden @ X11 @ X13)
% 0.90/1.08          | ~ (r2_hidden @ X9 @ X10))),
% 0.90/1.08      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         ((v1_xboole_0 @ X0)
% 0.90/1.08          | ~ (r2_hidden @ X2 @ X1)
% 0.90/1.08          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.90/1.08             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((v1_xboole_0 @ X0)
% 0.90/1.08          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.90/1.08             (k2_zfmisc_1 @ X0 @ X1))
% 0.90/1.08          | (v1_xboole_0 @ X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['2', '5'])).
% 0.90/1.08  thf('7', plain,
% 0.90/1.08      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_C_2 @ sk_A))
% 0.90/1.08        | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08           (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_C_2 @ sk_A)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_C_2 @ sk_A))))),
% 0.90/1.08      inference('split', [status(esa)], ['7'])).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X3 @ X4)
% 0.90/1.08          | (r2_hidden @ X3 @ X5)
% 0.90/1.08          | ~ (r1_tarski @ X4 @ X5))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      ((![X0 : $i]:
% 0.90/1.08          ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A))
% 0.90/1.08           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_C_2 @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      ((((v1_xboole_0 @ sk_A)
% 0.90/1.08         | (v1_xboole_0 @ sk_B_1)
% 0.90/1.08         | (r2_hidden @ (k4_tarski @ (sk_B @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.90/1.08            (k2_zfmisc_1 @ sk_C_2 @ sk_A))))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_C_2 @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['6', '10'])).
% 0.90/1.08  thf(t2_tarski, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.90/1.08       ( ( A ) = ( B ) ) ))).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      (![X7 : $i, X8 : $i]:
% 0.90/1.08         (((X8) = (X7))
% 0.90/1.08          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X7)
% 0.90/1.08          | (r2_hidden @ (sk_C_1 @ X7 @ X8) @ X8))),
% 0.90/1.08      inference('cnf', [status(esa)], [t2_tarski])).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 0.90/1.08          | ((X1) = (X0))
% 0.90/1.08          | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.08  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (((X0) != (k1_xboole_0))
% 0.90/1.08          | ~ (v1_xboole_0 @ X0)
% 0.90/1.08          | ~ (v1_xboole_0 @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.08  thf('19', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.90/1.08      inference('simplify', [status(thm)], ['18'])).
% 0.90/1.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.90/1.08  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.90/1.08  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.90/1.08      inference('simplify_reflect+', [status(thm)], ['19', '20'])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.90/1.08          (k2_zfmisc_1 @ sk_C_2 @ sk_A))
% 0.90/1.08         | (v1_xboole_0 @ sk_B_1)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_C_2 @ sk_A))))),
% 0.90/1.08      inference('clc', [status(thm)], ['11', '21'])).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (![X4 : $i, X6 : $i]:
% 0.90/1.08         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('24', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.08      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.08  thf('26', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('27', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.08      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_C_2 @ sk_A)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_C_2 @ sk_A))))),
% 0.90/1.08      inference('clc', [status(thm)], ['22', '27'])).
% 0.90/1.08  thf('29', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.08         ((r2_hidden @ X11 @ X12)
% 0.90/1.08          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 0.90/1.08      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.08  thf('30', plain,
% 0.90/1.08      (((r2_hidden @ (sk_B @ sk_A) @ sk_A))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_C_2 @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.90/1.08         ((r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X13))
% 0.90/1.08          | ~ (r2_hidden @ X11 @ X13)
% 0.90/1.08          | ~ (r2_hidden @ X9 @ X10))),
% 0.90/1.08      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      ((![X0 : $i, X1 : $i]:
% 0.90/1.08          (~ (r2_hidden @ X1 @ X0)
% 0.90/1.08           | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ sk_A)) @ 
% 0.90/1.08              (k2_zfmisc_1 @ X0 @ sk_A))))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_C_2 @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((v1_xboole_0 @ X0)
% 0.90/1.08          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.90/1.08             (k2_zfmisc_1 @ X0 @ X1))
% 0.90/1.08          | (v1_xboole_0 @ X1))),
% 0.90/1.08      inference('sup-', [status(thm)], ['2', '5'])).
% 0.90/1.08  thf('34', plain,
% 0.90/1.08      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_A @ sk_C_2)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('split', [status(esa)], ['7'])).
% 0.90/1.08  thf('35', plain,
% 0.90/1.08      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X3 @ X4)
% 0.90/1.08          | (r2_hidden @ X3 @ X5)
% 0.90/1.08          | ~ (r1_tarski @ X4 @ X5))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      ((![X0 : $i]:
% 0.90/1.08          ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))
% 0.90/1.08           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.08  thf('37', plain,
% 0.90/1.08      ((((v1_xboole_0 @ sk_B_1)
% 0.90/1.08         | (v1_xboole_0 @ sk_A)
% 0.90/1.08         | (r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.90/1.08            (k2_zfmisc_1 @ sk_A @ sk_C_2))))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['33', '36'])).
% 0.90/1.08  thf('38', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.08      inference('sup-', [status(thm)], ['25', '26'])).
% 0.90/1.08  thf('39', plain,
% 0.90/1.08      ((((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.90/1.08          (k2_zfmisc_1 @ sk_A @ sk_C_2))
% 0.90/1.08         | (v1_xboole_0 @ sk_A)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('clc', [status(thm)], ['37', '38'])).
% 0.90/1.08  thf('40', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.90/1.08      inference('simplify_reflect+', [status(thm)], ['19', '20'])).
% 0.90/1.08  thf('41', plain,
% 0.90/1.08      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_A @ sk_C_2)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('clc', [status(thm)], ['39', '40'])).
% 0.90/1.08  thf('42', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.08         ((r2_hidden @ X9 @ X10)
% 0.90/1.08          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 0.90/1.08      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.08  thf('43', plain,
% 0.90/1.08      (((r2_hidden @ (sk_B @ sk_A) @ sk_A))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['41', '42'])).
% 0.90/1.08  thf('44', plain,
% 0.90/1.08      (![X4 : $i, X6 : $i]:
% 0.90/1.08         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('45', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.90/1.08         ((r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X13))
% 0.90/1.08          | ~ (r2_hidden @ X11 @ X13)
% 0.90/1.08          | ~ (r2_hidden @ X9 @ X10))),
% 0.90/1.08      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.08  thf('46', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.08         ((r1_tarski @ X0 @ X1)
% 0.90/1.08          | ~ (r2_hidden @ X3 @ X2)
% 0.90/1.08          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.90/1.08             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.08  thf('47', plain,
% 0.90/1.08      ((![X0 : $i, X1 : $i]:
% 0.90/1.08          ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X1 @ X0)) @ 
% 0.90/1.08            (k2_zfmisc_1 @ sk_A @ X0))
% 0.90/1.08           | (r1_tarski @ X0 @ X1)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['43', '46'])).
% 0.90/1.08  thf('48', plain,
% 0.90/1.08      ((![X0 : $i]:
% 0.90/1.08          ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_2))
% 0.90/1.08           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.08  thf('49', plain,
% 0.90/1.08      ((![X0 : $i]:
% 0.90/1.08          ((r1_tarski @ sk_B_1 @ X0)
% 0.90/1.08           | (r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.90/1.08              (k2_zfmisc_1 @ sk_A @ sk_C_2))))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.08  thf('50', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.08         ((r2_hidden @ X11 @ X12)
% 0.90/1.08          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 0.90/1.08      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.08  thf('51', plain,
% 0.90/1.08      ((![X0 : $i]:
% 0.90/1.08          ((r1_tarski @ sk_B_1 @ X0)
% 0.90/1.08           | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_2)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.08  thf('52', plain,
% 0.90/1.08      (![X4 : $i, X6 : $i]:
% 0.90/1.08         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('53', plain,
% 0.90/1.08      ((((r1_tarski @ sk_B_1 @ sk_C_2) | (r1_tarski @ sk_B_1 @ sk_C_2)))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['51', '52'])).
% 0.90/1.08  thf('54', plain,
% 0.90/1.08      (((r1_tarski @ sk_B_1 @ sk_C_2))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_A @ sk_C_2))))),
% 0.90/1.08      inference('simplify', [status(thm)], ['53'])).
% 0.90/1.08  thf('55', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('56', plain,
% 0.90/1.08      (~
% 0.90/1.08       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.08  thf('57', plain,
% 0.90/1.08      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_C_2 @ sk_A))) | 
% 0.90/1.08       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_A @ sk_C_2)))),
% 0.90/1.08      inference('split', [status(esa)], ['7'])).
% 0.90/1.08  thf('58', plain,
% 0.90/1.08      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.90/1.08      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.90/1.08  thf('59', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ X0)
% 0.90/1.08          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ sk_A)) @ 
% 0.90/1.08             (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.90/1.08      inference('simpl_trail', [status(thm)], ['32', '58'])).
% 0.90/1.08  thf('60', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         ((r1_tarski @ X0 @ X1)
% 0.90/1.08          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ sk_A)) @ 
% 0.90/1.08             (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['1', '59'])).
% 0.90/1.08  thf('61', plain,
% 0.90/1.08      ((![X0 : $i]:
% 0.90/1.08          ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A))
% 0.90/1.08           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.90/1.08         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08               (k2_zfmisc_1 @ sk_C_2 @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.08  thf('62', plain,
% 0.90/1.08      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.90/1.08         (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.90/1.08      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.90/1.08  thf('63', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A))
% 0.90/1.08          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.90/1.08      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.90/1.08  thf('64', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ sk_B_1 @ X0)
% 0.90/1.08          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.90/1.08             (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['60', '63'])).
% 0.90/1.08  thf('65', plain,
% 0.90/1.08      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.08         ((r2_hidden @ X9 @ X10)
% 0.90/1.08          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 0.90/1.08      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.08  thf('66', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         ((r1_tarski @ sk_B_1 @ X0)
% 0.90/1.08          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_2))),
% 0.90/1.08      inference('sup-', [status(thm)], ['64', '65'])).
% 0.90/1.08  thf('67', plain,
% 0.90/1.08      (![X4 : $i, X6 : $i]:
% 0.90/1.08         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.90/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.08  thf('68', plain,
% 0.90/1.08      (((r1_tarski @ sk_B_1 @ sk_C_2) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.90/1.08      inference('sup-', [status(thm)], ['66', '67'])).
% 0.90/1.08  thf('69', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.90/1.08      inference('simplify', [status(thm)], ['68'])).
% 0.90/1.08  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
