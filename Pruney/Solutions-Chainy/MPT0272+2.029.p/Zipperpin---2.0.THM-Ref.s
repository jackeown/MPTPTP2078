%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.snkfdFac5V

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:29 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 159 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  718 (1414 expanded)
%              Number of equality atoms :   73 ( 146 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('13',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['24'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['24'])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['24'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','60'])).

thf('62',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.snkfdFac5V
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.75/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.95  % Solved by: fo/fo7.sh
% 0.75/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.95  % done 590 iterations in 0.504s
% 0.75/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.95  % SZS output start Refutation
% 0.75/0.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.95  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.75/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.95  thf(d5_xboole_0, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.75/0.95       ( ![D:$i]:
% 0.75/0.95         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.95           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.75/0.95  thf('0', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.95         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('1', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.75/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.95      inference('eq_fact', [status(thm)], ['0'])).
% 0.75/0.95  thf(d1_tarski, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.75/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.75/0.95  thf('2', plain,
% 0.75/0.95      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X15 @ X14)
% 0.75/0.95          | ((X15) = (X12))
% 0.75/0.95          | ((X14) != (k1_tarski @ X12)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d1_tarski])).
% 0.75/0.95  thf('3', plain,
% 0.75/0.95      (![X12 : $i, X15 : $i]:
% 0.75/0.95         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['2'])).
% 0.75/0.95  thf('4', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.75/0.95          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['1', '3'])).
% 0.75/0.95  thf('5', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.75/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.95      inference('eq_fact', [status(thm)], ['0'])).
% 0.75/0.95  thf('6', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.95         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.75/0.95          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.75/0.95          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('7', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.75/0.95          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.75/0.95          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.75/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['5', '6'])).
% 0.75/0.95  thf('8', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.75/0.95          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.75/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['7'])).
% 0.75/0.95  thf('9', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.75/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.95      inference('eq_fact', [status(thm)], ['0'])).
% 0.75/0.95  thf('10', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.75/0.95          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.75/0.95      inference('clc', [status(thm)], ['8', '9'])).
% 0.75/0.95  thf('11', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ X0 @ X1)
% 0.75/0.95          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.75/0.95          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['4', '10'])).
% 0.75/0.95  thf('12', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.75/0.95          | (r2_hidden @ X0 @ X1))),
% 0.75/0.95      inference('simplify', [status(thm)], ['11'])).
% 0.75/0.95  thf(t69_zfmisc_1, conjecture,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.75/0.95       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.95    (~( ![A:$i,B:$i]:
% 0.75/0.95        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.75/0.95          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.75/0.95    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.75/0.95  thf('13', plain,
% 0.75/0.95      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('14', plain,
% 0.75/0.95      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.95  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.75/0.95      inference('simplify', [status(thm)], ['14'])).
% 0.75/0.95  thf('16', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.95         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf(t2_boole, axiom,
% 0.75/0.95    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.75/0.95  thf('17', plain,
% 0.75/0.95      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [t2_boole])).
% 0.75/0.95  thf(t100_xboole_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.95  thf('18', plain,
% 0.75/0.95      (![X8 : $i, X9 : $i]:
% 0.75/0.95         ((k4_xboole_0 @ X8 @ X9)
% 0.75/0.95           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.95  thf('19', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.95      inference('sup+', [status(thm)], ['17', '18'])).
% 0.75/0.95  thf(t5_boole, axiom,
% 0.75/0.95    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.95  thf('20', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.75/0.95      inference('cnf', [status(esa)], [t5_boole])).
% 0.75/0.95  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.95      inference('demod', [status(thm)], ['19', '20'])).
% 0.75/0.95  thf('22', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X6 @ X5)
% 0.75/0.95          | ~ (r2_hidden @ X6 @ X4)
% 0.75/0.95          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('23', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X6 @ X4)
% 0.75/0.95          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['22'])).
% 0.75/0.95  thf('24', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['21', '23'])).
% 0.75/0.95  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.95      inference('condensation', [status(thm)], ['24'])).
% 0.75/0.95  thf('26', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.75/0.95          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['16', '25'])).
% 0.75/0.95  thf('27', plain,
% 0.75/0.95      (![X8 : $i, X9 : $i]:
% 0.75/0.95         ((k4_xboole_0 @ X8 @ X9)
% 0.75/0.95           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.95  thf(commutativity_k5_xboole_0, axiom,
% 0.75/0.95    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.75/0.95  thf('28', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.75/0.95      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.95  thf('29', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.75/0.95      inference('cnf', [status(esa)], [t5_boole])).
% 0.75/0.95  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.95      inference('sup+', [status(thm)], ['28', '29'])).
% 0.75/0.95  thf('31', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup+', [status(thm)], ['27', '30'])).
% 0.75/0.95  thf('32', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.75/0.95          | ((X1) = (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['26', '31'])).
% 0.75/0.95  thf('33', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.95         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.95      inference('condensation', [status(thm)], ['24'])).
% 0.75/0.95  thf('35', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.75/0.95          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.95  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.95      inference('condensation', [status(thm)], ['24'])).
% 0.75/0.95  thf('37', plain,
% 0.75/0.95      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['35', '36'])).
% 0.75/0.95  thf('38', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup+', [status(thm)], ['27', '30'])).
% 0.75/0.95  thf('39', plain,
% 0.75/0.95      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.75/0.95      inference('sup+', [status(thm)], ['37', '38'])).
% 0.75/0.95  thf('40', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.75/0.95          | ((X1) = (k1_xboole_0)))),
% 0.75/0.95      inference('demod', [status(thm)], ['32', '39'])).
% 0.75/0.95  thf('41', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X6 @ X5)
% 0.75/0.95          | (r2_hidden @ X6 @ X3)
% 0.75/0.95          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('42', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.95         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['41'])).
% 0.75/0.95  thf('43', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.75/0.95          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 0.75/0.95             X1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['40', '42'])).
% 0.75/0.95  thf('44', plain,
% 0.75/0.95      (![X12 : $i, X15 : $i]:
% 0.75/0.95         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['2'])).
% 0.75/0.95  thf('45', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 0.75/0.95          | ((sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 0.75/0.95              = (X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['43', '44'])).
% 0.75/0.95  thf('46', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.95         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('47', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.95         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.95          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('48', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.75/0.95          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.75/0.95          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.75/0.95          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['46', '47'])).
% 0.75/0.95  thf('49', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.75/0.95          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.75/0.95      inference('simplify', [status(thm)], ['48'])).
% 0.75/0.95  thf('50', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.75/0.95          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.95  thf('51', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.75/0.95         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.75/0.95          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.75/0.95          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.95  thf('52', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))
% 0.75/0.95          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.75/0.95          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/0.95  thf('53', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 0.75/0.95          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['52'])).
% 0.75/0.95  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.95      inference('condensation', [status(thm)], ['24'])).
% 0.75/0.95  thf('55', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.95      inference('clc', [status(thm)], ['53', '54'])).
% 0.75/0.95  thf('56', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.75/0.95      inference('demod', [status(thm)], ['49', '55'])).
% 0.75/0.95  thf('57', plain,
% 0.75/0.95      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X6 @ X4)
% 0.75/0.95          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['22'])).
% 0.75/0.95  thf('58', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.75/0.95          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.95  thf('59', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X0 @ X1)
% 0.75/0.95          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.75/0.95          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['45', '58'])).
% 0.75/0.95  thf('60', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i]:
% 0.75/0.95         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.75/0.95          | ~ (r2_hidden @ X0 @ X1))),
% 0.75/0.95      inference('simplify', [status(thm)], ['59'])).
% 0.75/0.95  thf('61', plain,
% 0.75/0.95      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.75/0.95      inference('sup-', [status(thm)], ['15', '60'])).
% 0.75/0.95  thf('62', plain,
% 0.75/0.95      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('63', plain, ($false),
% 0.75/0.95      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.75/0.95  
% 0.75/0.95  % SZS output end Refutation
% 0.75/0.95  
% 0.75/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
