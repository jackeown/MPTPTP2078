%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KIQbfVBisO

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:37 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 162 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  845 (1802 expanded)
%              Number of equality atoms :   59 ( 123 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k3_xboole_0 @ X12 @ X15 ) )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['44'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['43','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','67'])).

thf('69',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','68'])).

thf('70',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KIQbfVBisO
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 4.16/4.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.16/4.40  % Solved by: fo/fo7.sh
% 4.16/4.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.16/4.40  % done 4589 iterations in 3.956s
% 4.16/4.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.16/4.40  % SZS output start Refutation
% 4.16/4.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.16/4.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.16/4.40  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.16/4.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.16/4.40  thf(sk_A_type, type, sk_A: $i).
% 4.16/4.40  thf(sk_B_type, type, sk_B: $i).
% 4.16/4.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.16/4.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.16/4.40  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.16/4.40  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 4.16/4.40  thf(t48_xboole_1, axiom,
% 4.16/4.40    (![A:$i,B:$i]:
% 4.16/4.40     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.16/4.40  thf('0', plain,
% 4.16/4.40      (![X16 : $i, X17 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 4.16/4.40           = (k3_xboole_0 @ X16 @ X17))),
% 4.16/4.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.16/4.40  thf(d4_xboole_0, axiom,
% 4.16/4.40    (![A:$i,B:$i,C:$i]:
% 4.16/4.40     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 4.16/4.40       ( ![D:$i]:
% 4.16/4.40         ( ( r2_hidden @ D @ C ) <=>
% 4.16/4.40           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.16/4.40  thf('1', plain,
% 4.16/4.40      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.16/4.40         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 4.16/4.40          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 4.16/4.40          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.16/4.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.16/4.40  thf('2', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.40      inference('eq_fact', [status(thm)], ['1'])).
% 4.16/4.40  thf(d5_xboole_0, axiom,
% 4.16/4.40    (![A:$i,B:$i,C:$i]:
% 4.16/4.40     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.16/4.40       ( ![D:$i]:
% 4.16/4.40         ( ( r2_hidden @ D @ C ) <=>
% 4.16/4.40           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.16/4.40  thf('3', plain,
% 4.16/4.40      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X10 @ X9)
% 4.16/4.40          | (r2_hidden @ X10 @ X7)
% 4.16/4.40          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 4.16/4.40      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.16/4.40  thf('4', plain,
% 4.16/4.40      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.16/4.40         ((r2_hidden @ X10 @ X7)
% 4.16/4.40          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['3'])).
% 4.16/4.40  thf('5', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.40         (((k4_xboole_0 @ X1 @ X0)
% 4.16/4.40            = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 4.16/4.40          | (r2_hidden @ 
% 4.16/4.40             (sk_D @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0) @ X2) @ 
% 4.16/4.40             X1))),
% 4.16/4.40      inference('sup-', [status(thm)], ['2', '4'])).
% 4.16/4.40  thf('6', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.40      inference('eq_fact', [status(thm)], ['1'])).
% 4.16/4.40  thf('7', plain,
% 4.16/4.40      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.16/4.40         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.16/4.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.16/4.40  thf('8', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['6', '7'])).
% 4.16/4.40  thf('9', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['8'])).
% 4.16/4.40  thf('10', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.40      inference('eq_fact', [status(thm)], ['1'])).
% 4.16/4.40  thf('11', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 4.16/4.40      inference('clc', [status(thm)], ['9', '10'])).
% 4.16/4.40  thf('12', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         (((k4_xboole_0 @ X0 @ X1)
% 4.16/4.40            = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 4.16/4.40          | ((k4_xboole_0 @ X0 @ X1)
% 4.16/4.40              = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 4.16/4.40      inference('sup-', [status(thm)], ['5', '11'])).
% 4.16/4.40  thf('13', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X0 @ X1)
% 4.16/4.40           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['12'])).
% 4.16/4.40  thf(t4_xboole_0, axiom,
% 4.16/4.40    (![A:$i,B:$i]:
% 4.16/4.40     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.16/4.40            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.16/4.40       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.16/4.40            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.16/4.40  thf('14', plain,
% 4.16/4.40      (![X12 : $i, X13 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ X12 @ X13)
% 4.16/4.40          | (r2_hidden @ (sk_C @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 4.16/4.40      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.16/4.40  thf('15', plain,
% 4.16/4.40      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X4 @ X3)
% 4.16/4.40          | (r2_hidden @ X4 @ X1)
% 4.16/4.40          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 4.16/4.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.16/4.40  thf('16', plain,
% 4.16/4.40      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.16/4.40         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['15'])).
% 4.16/4.40  thf('17', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 4.16/4.40      inference('sup-', [status(thm)], ['14', '16'])).
% 4.16/4.40  thf(d1_tarski, axiom,
% 4.16/4.40    (![A:$i,B:$i]:
% 4.16/4.40     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 4.16/4.40       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 4.16/4.40  thf('18', plain,
% 4.16/4.40      (![X18 : $i, X20 : $i, X21 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X21 @ X20)
% 4.16/4.40          | ((X21) = (X18))
% 4.16/4.40          | ((X20) != (k1_tarski @ X18)))),
% 4.16/4.40      inference('cnf', [status(esa)], [d1_tarski])).
% 4.16/4.40  thf('19', plain,
% 4.16/4.40      (![X18 : $i, X21 : $i]:
% 4.16/4.40         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['18'])).
% 4.16/4.40  thf('20', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 4.16/4.40          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['17', '19'])).
% 4.16/4.40  thf('21', plain,
% 4.16/4.40      (![X12 : $i, X13 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ X12 @ X13)
% 4.16/4.40          | (r2_hidden @ (sk_C @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 4.16/4.40      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.16/4.40  thf('22', plain,
% 4.16/4.40      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X4 @ X3)
% 4.16/4.40          | (r2_hidden @ X4 @ X2)
% 4.16/4.40          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 4.16/4.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.16/4.40  thf('23', plain,
% 4.16/4.40      (![X1 : $i, X2 : $i, X4 : $i]:
% 4.16/4.40         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['22'])).
% 4.16/4.40  thf('24', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 4.16/4.40      inference('sup-', [status(thm)], ['21', '23'])).
% 4.16/4.40  thf('25', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ X0 @ X1)
% 4.16/4.40          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 4.16/4.40          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 4.16/4.40      inference('sup+', [status(thm)], ['20', '24'])).
% 4.16/4.40  thf('26', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 4.16/4.40      inference('simplify', [status(thm)], ['25'])).
% 4.16/4.40  thf(t58_zfmisc_1, conjecture,
% 4.16/4.40    (![A:$i,B:$i]:
% 4.16/4.40     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 4.16/4.40       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 4.16/4.40  thf(zf_stmt_0, negated_conjecture,
% 4.16/4.40    (~( ![A:$i,B:$i]:
% 4.16/4.40        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 4.16/4.40          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 4.16/4.40    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 4.16/4.40  thf('27', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 4.16/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.40  thf('28', plain, ((r2_hidden @ sk_A @ sk_B)),
% 4.16/4.40      inference('sup-', [status(thm)], ['26', '27'])).
% 4.16/4.40  thf('29', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 4.16/4.40          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['17', '19'])).
% 4.16/4.40  thf('30', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 4.16/4.40      inference('sup-', [status(thm)], ['21', '23'])).
% 4.16/4.40  thf('31', plain,
% 4.16/4.40      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X10 @ X9)
% 4.16/4.40          | ~ (r2_hidden @ X10 @ X8)
% 4.16/4.40          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 4.16/4.40      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.16/4.40  thf('32', plain,
% 4.16/4.40      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X10 @ X8)
% 4.16/4.40          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['31'])).
% 4.16/4.40  thf('33', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 4.16/4.40          | ~ (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 4.16/4.40      inference('sup-', [status(thm)], ['30', '32'])).
% 4.16/4.40  thf('34', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X0 @ X1)
% 4.16/4.40          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 4.16/4.40          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k4_xboole_0 @ X2 @ X1)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['29', '33'])).
% 4.16/4.40  thf('35', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.40         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 4.16/4.40          | ~ (r2_hidden @ X0 @ X1))),
% 4.16/4.40      inference('simplify', [status(thm)], ['34'])).
% 4.16/4.40  thf('36', plain,
% 4.16/4.40      (![X0 : $i]:
% 4.16/4.40         (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))),
% 4.16/4.40      inference('sup-', [status(thm)], ['28', '35'])).
% 4.16/4.40  thf('37', plain,
% 4.16/4.40      (![X7 : $i, X8 : $i, X11 : $i]:
% 4.16/4.40         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 4.16/4.40          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 4.16/4.40          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 4.16/4.40      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.16/4.40  thf('38', plain,
% 4.16/4.40      (![X7 : $i, X8 : $i, X11 : $i]:
% 4.16/4.40         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 4.16/4.40          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 4.16/4.40          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 4.16/4.40      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.16/4.40  thf('39', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ (sk_D_1 @ X1 @ X0 @ X0) @ X1)
% 4.16/4.40          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 4.16/4.40          | (r2_hidden @ (sk_D_1 @ X1 @ X0 @ X0) @ X1)
% 4.16/4.40          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['37', '38'])).
% 4.16/4.40  thf('40', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 4.16/4.40          | (r2_hidden @ (sk_D_1 @ X1 @ X0 @ X0) @ X1))),
% 4.16/4.40      inference('simplify', [status(thm)], ['39'])).
% 4.16/4.40  thf('41', plain,
% 4.16/4.40      (![X12 : $i, X14 : $i, X15 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X14 @ (k3_xboole_0 @ X12 @ X15))
% 4.16/4.40          | ~ (r1_xboole_0 @ X12 @ X15))),
% 4.16/4.40      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.16/4.40  thf('42', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.40         (((k3_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 4.16/4.40          | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.16/4.40      inference('sup-', [status(thm)], ['40', '41'])).
% 4.16/4.40  thf('43', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))
% 4.16/4.40           = (k4_xboole_0 @ X1 @ X1))),
% 4.16/4.40      inference('sup-', [status(thm)], ['36', '42'])).
% 4.16/4.40  thf('44', plain,
% 4.16/4.40      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.16/4.40         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 4.16/4.40          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.16/4.40          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.16/4.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.16/4.40  thf('45', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 4.16/4.40      inference('eq_fact', [status(thm)], ['44'])).
% 4.16/4.40  thf('46', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 4.16/4.40      inference('eq_fact', [status(thm)], ['44'])).
% 4.16/4.40  thf('47', plain,
% 4.16/4.40      (![X1 : $i, X2 : $i, X5 : $i]:
% 4.16/4.40         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 4.16/4.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.16/4.40  thf('48', plain,
% 4.16/4.40      (![X0 : $i]:
% 4.16/4.40         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 4.16/4.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['46', '47'])).
% 4.16/4.40  thf('49', plain,
% 4.16/4.40      (![X0 : $i]:
% 4.16/4.40         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['48'])).
% 4.16/4.40  thf('50', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.40      inference('eq_fact', [status(thm)], ['1'])).
% 4.16/4.40  thf('51', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.16/4.40      inference('clc', [status(thm)], ['49', '50'])).
% 4.16/4.40  thf('52', plain,
% 4.16/4.40      (![X16 : $i, X17 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 4.16/4.40           = (k3_xboole_0 @ X16 @ X17))),
% 4.16/4.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.16/4.40  thf('53', plain,
% 4.16/4.40      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X10 @ X8)
% 4.16/4.40          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['31'])).
% 4.16/4.40  thf('54', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.16/4.40          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['52', '53'])).
% 4.16/4.40  thf('55', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         (~ (r2_hidden @ X1 @ X0)
% 4.16/4.40          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['51', '54'])).
% 4.16/4.40  thf('56', plain,
% 4.16/4.40      (![X7 : $i, X8 : $i, X10 : $i]:
% 4.16/4.40         ((r2_hidden @ X10 @ X7)
% 4.16/4.40          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 4.16/4.40      inference('simplify', [status(thm)], ['3'])).
% 4.16/4.40  thf('57', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 4.16/4.40      inference('clc', [status(thm)], ['55', '56'])).
% 4.16/4.40  thf('58', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X0 @ X0)
% 4.16/4.40           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 4.16/4.40      inference('sup-', [status(thm)], ['45', '57'])).
% 4.16/4.40  thf('59', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 4.16/4.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.40      inference('eq_fact', [status(thm)], ['1'])).
% 4.16/4.40  thf('60', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 4.16/4.40      inference('clc', [status(thm)], ['55', '56'])).
% 4.16/4.40  thf('61', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X0 @ X0)
% 4.16/4.40           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 4.16/4.40      inference('sup-', [status(thm)], ['59', '60'])).
% 4.16/4.40  thf('62', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 4.16/4.40      inference('sup+', [status(thm)], ['58', '61'])).
% 4.16/4.40  thf('63', plain,
% 4.16/4.40      (![X16 : $i, X17 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 4.16/4.40           = (k3_xboole_0 @ X16 @ X17))),
% 4.16/4.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.16/4.40  thf('64', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 4.16/4.40           = (k3_xboole_0 @ X1 @ X1))),
% 4.16/4.40      inference('sup+', [status(thm)], ['62', '63'])).
% 4.16/4.40  thf('65', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.16/4.40      inference('clc', [status(thm)], ['49', '50'])).
% 4.16/4.40  thf('66', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 4.16/4.40      inference('demod', [status(thm)], ['64', '65'])).
% 4.16/4.40  thf('67', plain,
% 4.16/4.40      (![X0 : $i, X1 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X1 @ 
% 4.16/4.40           (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B)))
% 4.16/4.40           = (X1))),
% 4.16/4.40      inference('sup+', [status(thm)], ['43', '66'])).
% 4.16/4.40  thf('68', plain,
% 4.16/4.40      (![X0 : $i]:
% 4.16/4.40         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) = (X0))),
% 4.16/4.40      inference('sup+', [status(thm)], ['13', '67'])).
% 4.16/4.40  thf('69', plain,
% 4.16/4.40      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 4.16/4.40      inference('sup+', [status(thm)], ['0', '68'])).
% 4.16/4.40  thf('70', plain,
% 4.16/4.40      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 4.16/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.40  thf('71', plain, ($false),
% 4.16/4.40      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 4.16/4.40  
% 4.16/4.40  % SZS output end Refutation
% 4.16/4.40  
% 4.16/4.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
