%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HHz7VJdxPY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:03 EST 2020

% Result     : Theorem 4.98s
% Output     : Refutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 140 expanded)
%              Number of leaves         :   15 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  730 (1384 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t96_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t96_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X7 ) )
      | ( r2_hidden @ X4 @ X7 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k5_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

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

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) @ X1 )
      | ( r1_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(condensation,[status(thm)],['24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X7 ) )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','46'])).

thf('48',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HHz7VJdxPY
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:56:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.98/5.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.98/5.21  % Solved by: fo/fo7.sh
% 4.98/5.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.98/5.21  % done 3793 iterations in 4.746s
% 4.98/5.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.98/5.21  % SZS output start Refutation
% 4.98/5.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.98/5.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.98/5.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.98/5.21  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.98/5.21  thf(sk_A_type, type, sk_A: $i).
% 4.98/5.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.98/5.21  thf(sk_B_type, type, sk_B: $i).
% 4.98/5.21  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.98/5.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.98/5.21  thf(t96_xboole_1, conjecture,
% 4.98/5.21    (![A:$i,B:$i]:
% 4.98/5.21     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 4.98/5.21  thf(zf_stmt_0, negated_conjecture,
% 4.98/5.21    (~( ![A:$i,B:$i]:
% 4.98/5.21        ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )),
% 4.98/5.21    inference('cnf.neg', [status(esa)], [t96_xboole_1])).
% 4.98/5.21  thf('0', plain,
% 4.98/5.21      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 4.98/5.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.98/5.21  thf(d3_tarski, axiom,
% 4.98/5.21    (![A:$i,B:$i]:
% 4.98/5.21     ( ( r1_tarski @ A @ B ) <=>
% 4.98/5.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.98/5.21  thf('1', plain,
% 4.98/5.21      (![X1 : $i, X3 : $i]:
% 4.98/5.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf(t36_xboole_1, axiom,
% 4.98/5.21    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.98/5.21  thf('2', plain,
% 4.98/5.21      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 4.98/5.21      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.98/5.21  thf('3', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         (~ (r2_hidden @ X0 @ X1)
% 4.98/5.21          | (r2_hidden @ X0 @ X2)
% 4.98/5.21          | ~ (r1_tarski @ X1 @ X2))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf('4', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['2', '3'])).
% 4.98/5.21  thf('5', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 4.98/5.21          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 4.98/5.21      inference('sup-', [status(thm)], ['1', '4'])).
% 4.98/5.21  thf(t1_xboole_0, axiom,
% 4.98/5.21    (![A:$i,B:$i,C:$i]:
% 4.98/5.21     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 4.98/5.21       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 4.98/5.21  thf('6', plain,
% 4.98/5.21      (![X4 : $i, X5 : $i, X7 : $i]:
% 4.98/5.21         ((r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X7))
% 4.98/5.21          | (r2_hidden @ X4 @ X7)
% 4.98/5.21          | ~ (r2_hidden @ X4 @ X5))),
% 4.98/5.21      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.98/5.21  thf('7', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.98/5.21         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 4.98/5.21          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X3)
% 4.98/5.21          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 4.98/5.21             (k5_xboole_0 @ X0 @ X3)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['5', '6'])).
% 4.98/5.21  thf('8', plain,
% 4.98/5.21      (![X1 : $i, X3 : $i]:
% 4.98/5.21         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf('9', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r2_hidden @ 
% 4.98/5.21           (sk_C @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)) @ X0)
% 4.98/5.21          | (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k5_xboole_0 @ X1 @ X0))
% 4.98/5.21          | (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k5_xboole_0 @ X1 @ X0)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['7', '8'])).
% 4.98/5.21  thf('10', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k5_xboole_0 @ X1 @ X0))
% 4.98/5.21          | (r2_hidden @ 
% 4.98/5.21             (sk_C @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)) @ X0))),
% 4.98/5.21      inference('simplify', [status(thm)], ['9'])).
% 4.98/5.21  thf(t3_xboole_0, axiom,
% 4.98/5.21    (![A:$i,B:$i]:
% 4.98/5.21     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 4.98/5.21            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.98/5.21       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.98/5.21            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 4.98/5.21  thf('11', plain,
% 4.98/5.21      (![X8 : $i, X9 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 4.98/5.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.98/5.21  thf('12', plain,
% 4.98/5.21      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.98/5.21         ((r2_hidden @ X4 @ X5)
% 4.98/5.21          | (r2_hidden @ X4 @ X6)
% 4.98/5.21          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 4.98/5.21      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.98/5.21  thf('13', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 4.98/5.21          | (r2_hidden @ (sk_C_1 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 4.98/5.21          | (r2_hidden @ (sk_C_1 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 4.98/5.21      inference('sup-', [status(thm)], ['11', '12'])).
% 4.98/5.21  thf(t79_xboole_1, axiom,
% 4.98/5.21    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.98/5.21  thf('14', plain,
% 4.98/5.21      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 4.98/5.21      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.98/5.21  thf('15', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 4.98/5.21          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 4.98/5.21      inference('sup-', [status(thm)], ['1', '4'])).
% 4.98/5.21  thf('16', plain,
% 4.98/5.21      (![X1 : $i, X3 : $i]:
% 4.98/5.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf('17', plain,
% 4.98/5.21      (![X8 : $i, X10 : $i, X11 : $i]:
% 4.98/5.21         (~ (r2_hidden @ X10 @ X8)
% 4.98/5.21          | ~ (r2_hidden @ X10 @ X11)
% 4.98/5.21          | ~ (r1_xboole_0 @ X8 @ X11))),
% 4.98/5.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.98/5.21  thf('18', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_tarski @ X0 @ X1)
% 4.98/5.21          | ~ (r1_xboole_0 @ X0 @ X2)
% 4.98/5.21          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 4.98/5.21      inference('sup-', [status(thm)], ['16', '17'])).
% 4.98/5.21  thf('19', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 4.98/5.21          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 4.98/5.21          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 4.98/5.21      inference('sup-', [status(thm)], ['15', '18'])).
% 4.98/5.21  thf('20', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 4.98/5.21          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 4.98/5.21      inference('simplify', [status(thm)], ['19'])).
% 4.98/5.21  thf('21', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 4.98/5.21      inference('sup-', [status(thm)], ['14', '20'])).
% 4.98/5.21  thf('22', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         (~ (r2_hidden @ X0 @ X1)
% 4.98/5.21          | (r2_hidden @ X0 @ X2)
% 4.98/5.21          | ~ (r1_tarski @ X1 @ X2))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf('23', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X1)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['21', '22'])).
% 4.98/5.21  thf('24', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.98/5.21         ((r2_hidden @ 
% 4.98/5.21           (sk_C_1 @ X2 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)) @ X1)
% 4.98/5.21          | (r1_xboole_0 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) @ X2)
% 4.98/5.21          | (r2_hidden @ 
% 4.98/5.21             (sk_C_1 @ X2 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)) @ X3))),
% 4.98/5.21      inference('sup-', [status(thm)], ['13', '23'])).
% 4.98/5.21  thf('25', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r2_hidden @ 
% 4.98/5.21           (sk_C_1 @ X2 @ (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)) @ X0)
% 4.98/5.21          | (r1_xboole_0 @ (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) @ X2))),
% 4.98/5.21      inference('condensation', [status(thm)], ['24'])).
% 4.98/5.21  thf('26', plain,
% 4.98/5.21      (![X8 : $i, X9 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X9))),
% 4.98/5.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.98/5.21  thf('27', plain,
% 4.98/5.21      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 4.98/5.21      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.98/5.21  thf('28', plain,
% 4.98/5.21      (![X8 : $i, X9 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 4.98/5.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.98/5.21  thf('29', plain,
% 4.98/5.21      (![X8 : $i, X9 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X9))),
% 4.98/5.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.98/5.21  thf('30', plain,
% 4.98/5.21      (![X8 : $i, X10 : $i, X11 : $i]:
% 4.98/5.21         (~ (r2_hidden @ X10 @ X8)
% 4.98/5.21          | ~ (r2_hidden @ X10 @ X11)
% 4.98/5.21          | ~ (r1_xboole_0 @ X8 @ X11))),
% 4.98/5.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.98/5.21  thf('31', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X1 @ X0)
% 4.98/5.21          | ~ (r1_xboole_0 @ X0 @ X2)
% 4.98/5.21          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 4.98/5.21      inference('sup-', [status(thm)], ['29', '30'])).
% 4.98/5.21  thf('32', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X0 @ X1)
% 4.98/5.21          | ~ (r1_xboole_0 @ X1 @ X0)
% 4.98/5.21          | (r1_xboole_0 @ X0 @ X1))),
% 4.98/5.21      inference('sup-', [status(thm)], ['28', '31'])).
% 4.98/5.21  thf('33', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 4.98/5.21      inference('simplify', [status(thm)], ['32'])).
% 4.98/5.21  thf('34', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.98/5.21      inference('sup-', [status(thm)], ['27', '33'])).
% 4.98/5.21  thf('35', plain,
% 4.98/5.21      (![X1 : $i, X3 : $i]:
% 4.98/5.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf('36', plain,
% 4.98/5.21      (![X4 : $i, X5 : $i, X7 : $i]:
% 4.98/5.21         ((r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X7))
% 4.98/5.21          | (r2_hidden @ X4 @ X5)
% 4.98/5.21          | ~ (r2_hidden @ X4 @ X7))),
% 4.98/5.21      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.98/5.21  thf('37', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_tarski @ X0 @ X1)
% 4.98/5.21          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 4.98/5.21          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X2 @ X0)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['35', '36'])).
% 4.98/5.21  thf('38', plain,
% 4.98/5.21      (![X1 : $i, X3 : $i]:
% 4.98/5.21         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf('39', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         ((r2_hidden @ (sk_C @ (k5_xboole_0 @ X1 @ X0) @ X0) @ X1)
% 4.98/5.21          | (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 4.98/5.21          | (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['37', '38'])).
% 4.98/5.21  thf('40', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         ((r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 4.98/5.21          | (r2_hidden @ (sk_C @ (k5_xboole_0 @ X1 @ X0) @ X0) @ X1))),
% 4.98/5.21      inference('simplify', [status(thm)], ['39'])).
% 4.98/5.21  thf('41', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_tarski @ X0 @ X1)
% 4.98/5.21          | ~ (r1_xboole_0 @ X0 @ X2)
% 4.98/5.21          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 4.98/5.21      inference('sup-', [status(thm)], ['16', '17'])).
% 4.98/5.21  thf('42', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         ((r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 4.98/5.21          | ~ (r1_xboole_0 @ X1 @ X0)
% 4.98/5.21          | (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['40', '41'])).
% 4.98/5.21  thf('43', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         (~ (r1_xboole_0 @ X1 @ X0)
% 4.98/5.21          | (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 4.98/5.21      inference('simplify', [status(thm)], ['42'])).
% 4.98/5.21  thf('44', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         (r1_tarski @ X0 @ (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 4.98/5.21      inference('sup-', [status(thm)], ['34', '43'])).
% 4.98/5.21  thf('45', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         (~ (r2_hidden @ X0 @ X1)
% 4.98/5.21          | (r2_hidden @ X0 @ X2)
% 4.98/5.21          | ~ (r1_tarski @ X1 @ X2))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf('46', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r2_hidden @ X2 @ (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 4.98/5.21          | ~ (r2_hidden @ X2 @ X0))),
% 4.98/5.21      inference('sup-', [status(thm)], ['44', '45'])).
% 4.98/5.21  thf('47', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X1 @ X0)
% 4.98/5.21          | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ 
% 4.98/5.21             (k5_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X0)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['26', '46'])).
% 4.98/5.21  thf('48', plain,
% 4.98/5.21      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.98/5.21         (~ (r2_hidden @ X4 @ X5)
% 4.98/5.21          | ~ (r2_hidden @ X4 @ X6)
% 4.98/5.21          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 4.98/5.21      inference('cnf', [status(esa)], [t1_xboole_0])).
% 4.98/5.21  thf('49', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X2 @ X0)
% 4.98/5.21          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X2) @ X0)
% 4.98/5.21          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['47', '48'])).
% 4.98/5.21  thf('50', plain,
% 4.98/5.21      (![X8 : $i, X9 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X9))),
% 4.98/5.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.98/5.21  thf('51', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         (~ (r2_hidden @ (sk_C_1 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 4.98/5.21          | (r1_xboole_0 @ X2 @ X0))),
% 4.98/5.21      inference('clc', [status(thm)], ['49', '50'])).
% 4.98/5.21  thf('52', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_xboole_0 @ 
% 4.98/5.21           (k5_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.98/5.21           X0)
% 4.98/5.21          | (r1_xboole_0 @ 
% 4.98/5.21             (k5_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.98/5.21             X0))),
% 4.98/5.21      inference('sup-', [status(thm)], ['25', '51'])).
% 4.98/5.21  thf('53', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         (r1_xboole_0 @ 
% 4.98/5.21          (k5_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.98/5.21          X0)),
% 4.98/5.21      inference('simplify', [status(thm)], ['52'])).
% 4.98/5.21  thf('54', plain,
% 4.98/5.21      (![X1 : $i, X3 : $i]:
% 4.98/5.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.98/5.21      inference('cnf', [status(esa)], [d3_tarski])).
% 4.98/5.21  thf('55', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r2_hidden @ X2 @ (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 4.98/5.21          | ~ (r2_hidden @ X2 @ X0))),
% 4.98/5.21      inference('sup-', [status(thm)], ['44', '45'])).
% 4.98/5.21  thf('56', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         ((r1_tarski @ X0 @ X1)
% 4.98/5.21          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 4.98/5.21             (k5_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X0)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['54', '55'])).
% 4.98/5.21  thf('57', plain,
% 4.98/5.21      (![X8 : $i, X10 : $i, X11 : $i]:
% 4.98/5.21         (~ (r2_hidden @ X10 @ X8)
% 4.98/5.21          | ~ (r2_hidden @ X10 @ X11)
% 4.98/5.21          | ~ (r1_xboole_0 @ X8 @ X11))),
% 4.98/5.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.98/5.21  thf('58', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.98/5.21         ((r1_tarski @ X0 @ X2)
% 4.98/5.21          | ~ (r1_xboole_0 @ (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ X3)
% 4.98/5.21          | ~ (r2_hidden @ (sk_C @ X2 @ X0) @ X3))),
% 4.98/5.21      inference('sup-', [status(thm)], ['56', '57'])).
% 4.98/5.21  thf('59', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.98/5.21         (~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 4.98/5.21          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 4.98/5.21      inference('sup-', [status(thm)], ['53', '58'])).
% 4.98/5.21  thf('60', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 4.98/5.21          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 4.98/5.21      inference('sup-', [status(thm)], ['10', '59'])).
% 4.98/5.21  thf('61', plain,
% 4.98/5.21      (![X0 : $i, X1 : $i]:
% 4.98/5.21         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))),
% 4.98/5.21      inference('simplify', [status(thm)], ['60'])).
% 4.98/5.21  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 4.98/5.21  
% 4.98/5.21  % SZS output end Refutation
% 4.98/5.21  
% 5.06/5.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
