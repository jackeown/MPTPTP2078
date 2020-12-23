%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MoxnPhub8u

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:21 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 199 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  783 (1989 expanded)
%              Number of equality atoms :   71 ( 170 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t52_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
          = ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X36: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ X38 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','32'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','16'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ( X13
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 @ X9 ) @ X9 )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ( X13
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X13 @ X10 @ X9 ) @ X10 )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X10 @ X9 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('59',plain,(
    ! [X36: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ X38 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('60',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) )
    | ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','69'])).

thf('71',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(demod,[status(thm)],['42','70'])).

thf('72',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['8','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MoxnPhub8u
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 693 iterations in 0.363s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.61/0.81  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.81  thf(t52_zfmisc_1, conjecture,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r2_hidden @ A @ B ) =>
% 0.61/0.81       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i,B:$i]:
% 0.61/0.81        ( ( r2_hidden @ A @ B ) =>
% 0.61/0.81          ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t52_zfmisc_1])).
% 0.61/0.81  thf('0', plain,
% 0.61/0.81      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(l35_zfmisc_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.61/0.81       ( r2_hidden @ A @ B ) ))).
% 0.61/0.81  thf('2', plain,
% 0.61/0.81      (![X36 : $i, X38 : $i]:
% 0.61/0.81         (((k4_xboole_0 @ (k1_tarski @ X36) @ X38) = (k1_xboole_0))
% 0.61/0.81          | ~ (r2_hidden @ X36 @ X38))),
% 0.61/0.81      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.61/0.81  thf('3', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.81  thf(t48_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('4', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.61/0.81           = (k3_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('5', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.61/0.81         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.61/0.81      inference('sup+', [status(thm)], ['3', '4'])).
% 0.61/0.81  thf(commutativity_k3_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.61/0.81  thf('6', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('7', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.61/0.81         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.61/0.81      inference('demod', [status(thm)], ['5', '6'])).
% 0.61/0.81  thf('8', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['0', '7'])).
% 0.61/0.81  thf(d4_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.61/0.81       ( ![D:$i]:
% 0.61/0.81         ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.81           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.61/0.81         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.61/0.81          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.61/0.81          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.61/0.81      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.61/0.81  thf('10', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.61/0.81          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.61/0.81      inference('eq_fact', [status(thm)], ['9'])).
% 0.61/0.81  thf('11', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.61/0.81          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.61/0.81      inference('eq_fact', [status(thm)], ['9'])).
% 0.61/0.81  thf('12', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.61/0.81         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.61/0.81          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.61/0.81          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.61/0.81          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.61/0.81      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.61/0.81  thf('13', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.61/0.81          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.61/0.81          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.61/0.81          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['11', '12'])).
% 0.61/0.81  thf('14', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.61/0.81          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.61/0.81      inference('simplify', [status(thm)], ['13'])).
% 0.61/0.81  thf('15', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.61/0.81         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.61/0.81          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.61/0.81          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.61/0.81      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.61/0.81  thf('16', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.61/0.81          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('eq_fact', [status(thm)], ['15'])).
% 0.61/0.81  thf('17', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('clc', [status(thm)], ['14', '16'])).
% 0.61/0.81  thf('18', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.61/0.81           = (k3_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf(d5_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.61/0.81       ( ![D:$i]:
% 0.61/0.81         ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.81           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.61/0.81  thf('19', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X12 @ X11)
% 0.61/0.81          | ~ (r2_hidden @ X12 @ X10)
% 0.61/0.81          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.61/0.81      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X12 @ X10)
% 0.61/0.81          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.61/0.81      inference('simplify', [status(thm)], ['19'])).
% 0.61/0.81  thf('21', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.61/0.81          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['18', '20'])).
% 0.61/0.81  thf('22', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X1 @ X0)
% 0.61/0.81          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['17', '21'])).
% 0.61/0.81  thf(t21_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.61/0.81  thf('23', plain,
% 0.61/0.81      (![X14 : $i, X15 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (X14))),
% 0.61/0.81      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.61/0.81  thf('24', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.61/0.81           = (k3_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('25', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.61/0.81           = (k3_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('26', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['24', '25'])).
% 0.61/0.81  thf('27', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X0 @ X0)
% 0.61/0.81           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 0.61/0.81      inference('sup+', [status(thm)], ['23', '26'])).
% 0.61/0.81  thf('28', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X6 @ X5)
% 0.61/0.81          | (r2_hidden @ X6 @ X4)
% 0.61/0.81          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.61/0.81      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.61/0.81  thf('30', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.61/0.81         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.61/0.81      inference('simplify', [status(thm)], ['29'])).
% 0.61/0.81  thf('31', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.61/0.81      inference('sup-', [status(thm)], ['28', '30'])).
% 0.61/0.81  thf('32', plain,
% 0.61/0.81      (![X0 : $i, X2 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0)) | (r2_hidden @ X2 @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['27', '31'])).
% 0.61/0.81  thf('33', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('clc', [status(thm)], ['22', '32'])).
% 0.61/0.81  thf('34', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X0 @ X0)
% 0.61/0.81           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.61/0.81      inference('sup-', [status(thm)], ['10', '33'])).
% 0.61/0.81  thf('35', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.61/0.81          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('eq_fact', [status(thm)], ['15'])).
% 0.61/0.81  thf('36', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('clc', [status(thm)], ['22', '32'])).
% 0.61/0.81  thf('37', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X0 @ X0)
% 0.61/0.81           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['35', '36'])).
% 0.61/0.81  thf('38', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['34', '37'])).
% 0.61/0.81  thf('39', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.61/0.81           = (k3_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('40', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.61/0.81           = (k3_xboole_0 @ X1 @ X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['38', '39'])).
% 0.61/0.81  thf('41', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('clc', [status(thm)], ['14', '16'])).
% 0.61/0.81  thf('42', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.61/0.81      inference('demod', [status(thm)], ['40', '41'])).
% 0.61/0.81  thf('43', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.61/0.81         (((X13) = (k4_xboole_0 @ X9 @ X10))
% 0.61/0.81          | (r2_hidden @ (sk_D_1 @ X13 @ X10 @ X9) @ X9)
% 0.61/0.81          | (r2_hidden @ (sk_D_1 @ X13 @ X10 @ X9) @ X13))),
% 0.61/0.81      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.61/0.81  thf('44', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.61/0.81         (((X13) = (k4_xboole_0 @ X9 @ X10))
% 0.61/0.81          | ~ (r2_hidden @ (sk_D_1 @ X13 @ X10 @ X9) @ X10)
% 0.61/0.81          | (r2_hidden @ (sk_D_1 @ X13 @ X10 @ X9) @ X13))),
% 0.61/0.81      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.61/0.81  thf('45', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r2_hidden @ (sk_D_1 @ X1 @ X0 @ X0) @ X1)
% 0.61/0.81          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.61/0.81          | (r2_hidden @ (sk_D_1 @ X1 @ X0 @ X0) @ X1)
% 0.61/0.81          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['43', '44'])).
% 0.61/0.81  thf('46', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.61/0.81          | (r2_hidden @ (sk_D_1 @ X1 @ X0 @ X0) @ X1))),
% 0.61/0.81      inference('simplify', [status(thm)], ['45'])).
% 0.61/0.81  thf('47', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.61/0.81         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.61/0.81          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.61/0.81          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.61/0.81      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.61/0.81  thf('48', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.61/0.81          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('eq_fact', [status(thm)], ['15'])).
% 0.61/0.81  thf('49', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.81  thf('50', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X12 @ X10)
% 0.61/0.81          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.61/0.81      inference('simplify', [status(thm)], ['19'])).
% 0.61/0.81  thf('51', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['49', '50'])).
% 0.61/0.81  thf('52', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.61/0.81          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['48', '51'])).
% 0.61/0.81  thf('53', plain,
% 0.61/0.81      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ k1_xboole_0)
% 0.61/0.81        | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ k1_xboole_0))
% 0.61/0.81        | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['47', '52'])).
% 0.61/0.81  thf('54', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('55', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('56', plain,
% 0.61/0.81      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ k1_xboole_0)
% 0.61/0.81        | ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.61/0.81        | ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.61/0.81  thf('57', plain,
% 0.61/0.81      ((((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.61/0.81        | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ k1_xboole_0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['56'])).
% 0.61/0.81  thf('58', plain,
% 0.61/0.81      ((((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.61/0.81        | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B) @ k1_xboole_0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['56'])).
% 0.61/0.81  thf('59', plain,
% 0.61/0.81      (![X36 : $i, X38 : $i]:
% 0.61/0.81         (((k4_xboole_0 @ (k1_tarski @ X36) @ X38) = (k1_xboole_0))
% 0.61/0.81          | ~ (r2_hidden @ X36 @ X38))),
% 0.61/0.81      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.61/0.81  thf('60', plain,
% 0.61/0.81      ((((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.61/0.81        | ((k4_xboole_0 @ 
% 0.61/0.81            (k1_tarski @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_B)) @ 
% 0.61/0.81            k1_xboole_0) = (k1_xboole_0)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['58', '59'])).
% 0.61/0.81  thf('61', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X12 @ X10)
% 0.61/0.81          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.61/0.81      inference('simplify', [status(thm)], ['19'])).
% 0.61/0.81  thf('62', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.61/0.81          | ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.61/0.81          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['60', '61'])).
% 0.61/0.81  thf('63', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.61/0.81          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.61/0.81      inference('simplify', [status(thm)], ['62'])).
% 0.61/0.81  thf('64', plain,
% 0.61/0.81      ((((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.61/0.81        | ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['57', '63'])).
% 0.61/0.81  thf('65', plain, (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ sk_B))),
% 0.61/0.81      inference('simplify', [status(thm)], ['64'])).
% 0.61/0.81  thf('66', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.61/0.81         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.61/0.81      inference('simplify', [status(thm)], ['29'])).
% 0.61/0.81  thf('67', plain,
% 0.61/0.81      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | (r2_hidden @ X0 @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['65', '66'])).
% 0.61/0.81  thf('68', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['49', '50'])).
% 0.61/0.81  thf('69', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.61/0.81      inference('clc', [status(thm)], ['67', '68'])).
% 0.61/0.81  thf('70', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['46', '69'])).
% 0.61/0.81  thf('71', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.61/0.81      inference('demod', [status(thm)], ['42', '70'])).
% 0.61/0.81  thf('72', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['8', '71'])).
% 0.61/0.81  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.61/0.81  
% 0.61/0.81  % SZS output end Refutation
% 0.61/0.81  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
