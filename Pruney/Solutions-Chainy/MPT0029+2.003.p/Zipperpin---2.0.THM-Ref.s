%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfYkg5l05r

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:52 EST 2020

% Result     : Theorem 36.10s
% Output     : Refutation 36.10s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 426 expanded)
%              Number of leaves         :   10 ( 110 expanded)
%              Depth                    :   19
%              Number of atoms          : 1306 (6668 expanded)
%              Number of equality atoms :   97 ( 447 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t22_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t22_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('3',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X3 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X1 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( X3
        = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1
        = ( k3_xboole_0 @ X2 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X1 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['36'])).

thf('44',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['36'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) )
      | ( X2
        = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X2
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','33'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','33'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X2
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['36'])).

thf('60',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('61',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k2_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['64','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','86'])).

thf('88',plain,(
    $false ),
    inference(simplify,[status(thm)],['87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfYkg5l05r
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:22:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 36.10/36.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 36.10/36.30  % Solved by: fo/fo7.sh
% 36.10/36.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 36.10/36.30  % done 17879 iterations in 35.854s
% 36.10/36.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 36.10/36.30  % SZS output start Refutation
% 36.10/36.30  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 36.10/36.30  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 36.10/36.30  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 36.10/36.30  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 36.10/36.30  thf(sk_B_type, type, sk_B: $i).
% 36.10/36.30  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 36.10/36.30  thf(sk_A_type, type, sk_A: $i).
% 36.10/36.30  thf(t22_xboole_1, conjecture,
% 36.10/36.30    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 36.10/36.30  thf(zf_stmt_0, negated_conjecture,
% 36.10/36.30    (~( ![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ) )),
% 36.10/36.30    inference('cnf.neg', [status(esa)], [t22_xboole_1])).
% 36.10/36.30  thf('0', plain,
% 36.10/36.30      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 36.10/36.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 36.10/36.30  thf(d4_xboole_0, axiom,
% 36.10/36.30    (![A:$i,B:$i,C:$i]:
% 36.10/36.30     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 36.10/36.30       ( ![D:$i]:
% 36.10/36.30         ( ( r2_hidden @ D @ C ) <=>
% 36.10/36.30           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 36.10/36.30  thf('1', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X11 : $i]:
% 36.10/36.30         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 36.10/36.30      inference('cnf', [status(esa)], [d4_xboole_0])).
% 36.10/36.30  thf('2', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['1'])).
% 36.10/36.30  thf('3', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X11 : $i]:
% 36.10/36.30         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 36.10/36.30      inference('cnf', [status(esa)], [d4_xboole_0])).
% 36.10/36.30  thf('4', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 36.10/36.30         (~ (r2_hidden @ X10 @ X9)
% 36.10/36.30          | (r2_hidden @ X10 @ X7)
% 36.10/36.30          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 36.10/36.30      inference('cnf', [status(esa)], [d4_xboole_0])).
% 36.10/36.30  thf('5', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X10 : $i]:
% 36.10/36.30         ((r2_hidden @ X10 @ X7)
% 36.10/36.30          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['4'])).
% 36.10/36.30  thf('6', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X3)
% 36.10/36.30          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X2 @ X3))
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X1))),
% 36.10/36.30      inference('sup-', [status(thm)], ['3', '5'])).
% 36.10/36.30  thf('7', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X0)
% 36.10/36.30          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['6'])).
% 36.10/36.30  thf('8', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X11 : $i]:
% 36.10/36.30         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 36.10/36.30      inference('cnf', [status(esa)], [d4_xboole_0])).
% 36.10/36.30  thf('9', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         (((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ 
% 36.10/36.30               (k3_xboole_0 @ X0 @ X2))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X1)
% 36.10/36.30          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['7', '8'])).
% 36.10/36.30  thf('10', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         (~ (r2_hidden @ (sk_D_1 @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X1)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ 
% 36.10/36.30               (k3_xboole_0 @ X0 @ X2))
% 36.10/36.30          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['9'])).
% 36.10/36.30  thf('11', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((k3_xboole_0 @ X1 @ X0)
% 36.10/36.30            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 36.10/36.30          | ((k3_xboole_0 @ X1 @ X0)
% 36.10/36.30              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 36.10/36.30          | ~ (r2_hidden @ 
% 36.10/36.30               (sk_D_1 @ (k3_xboole_0 @ X1 @ X0) @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 36.10/36.30               (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['2', '10'])).
% 36.10/36.30  thf('12', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (~ (r2_hidden @ 
% 36.10/36.30             (sk_D_1 @ (k3_xboole_0 @ X1 @ X0) @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 36.10/36.30             (k3_xboole_0 @ X1 @ X0))
% 36.10/36.30          | ((k3_xboole_0 @ X1 @ X0)
% 36.10/36.30              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['11'])).
% 36.10/36.30  thf('13', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['1'])).
% 36.10/36.30  thf('14', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((k3_xboole_0 @ X1 @ X0)
% 36.10/36.30           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 36.10/36.30      inference('clc', [status(thm)], ['12', '13'])).
% 36.10/36.30  thf('15', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((k3_xboole_0 @ X1 @ X0)
% 36.10/36.30           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 36.10/36.30      inference('clc', [status(thm)], ['12', '13'])).
% 36.10/36.30  thf(d3_xboole_0, axiom,
% 36.10/36.30    (![A:$i,B:$i,C:$i]:
% 36.10/36.30     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 36.10/36.30       ( ![D:$i]:
% 36.10/36.30         ( ( r2_hidden @ D @ C ) <=>
% 36.10/36.30           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 36.10/36.30  thf('16', plain,
% 36.10/36.30      (![X1 : $i, X3 : $i, X5 : $i]:
% 36.10/36.30         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 36.10/36.30          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 36.10/36.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 36.10/36.30  thf('17', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 36.10/36.30         (~ (r2_hidden @ X10 @ X9)
% 36.10/36.30          | (r2_hidden @ X10 @ X8)
% 36.10/36.30          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 36.10/36.30      inference('cnf', [status(esa)], [d4_xboole_0])).
% 36.10/36.30  thf('18', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X10 : $i]:
% 36.10/36.30         ((r2_hidden @ X10 @ X8)
% 36.10/36.30          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['17'])).
% 36.10/36.30  thf('19', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 36.10/36.30          | ((X3) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 36.10/36.30          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 36.10/36.30      inference('sup-', [status(thm)], ['16', '18'])).
% 36.10/36.30  thf('20', plain,
% 36.10/36.30      (![X1 : $i, X3 : $i, X5 : $i]:
% 36.10/36.30         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 36.10/36.30          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 36.10/36.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 36.10/36.30  thf('21', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 36.10/36.30          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['20'])).
% 36.10/36.30  thf('22', plain,
% 36.10/36.30      (![X1 : $i, X3 : $i, X5 : $i]:
% 36.10/36.30         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 36.10/36.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 36.10/36.30  thf('23', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 36.10/36.30          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['21', '22'])).
% 36.10/36.30  thf('24', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 36.10/36.30          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['23'])).
% 36.10/36.30  thf('25', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 36.10/36.30          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['20'])).
% 36.10/36.30  thf('26', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 36.10/36.30          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 36.10/36.30      inference('clc', [status(thm)], ['24', '25'])).
% 36.10/36.30  thf('27', plain,
% 36.10/36.30      (![X1 : $i, X3 : $i, X5 : $i]:
% 36.10/36.30         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 36.10/36.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 36.10/36.30  thf('28', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 36.10/36.30          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['26', '27'])).
% 36.10/36.30  thf('29', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 36.10/36.30          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['28'])).
% 36.10/36.30  thf('30', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 36.10/36.30          | (r2_hidden @ (sk_D @ X0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 36.10/36.30          | (r2_hidden @ (sk_D @ X0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 36.10/36.30          | ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['19', '29'])).
% 36.10/36.30  thf('31', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D @ X0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 36.10/36.30          | ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['30'])).
% 36.10/36.30  thf('32', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 36.10/36.30          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['28'])).
% 36.10/36.30  thf('33', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 36.10/36.30      inference('clc', [status(thm)], ['31', '32'])).
% 36.10/36.30  thf('34', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 36.10/36.30      inference('sup+', [status(thm)], ['15', '33'])).
% 36.10/36.30  thf('35', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 36.10/36.30      inference('clc', [status(thm)], ['31', '32'])).
% 36.10/36.30  thf('36', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X11 : $i]:
% 36.10/36.30         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 36.10/36.30      inference('cnf', [status(esa)], [d4_xboole_0])).
% 36.10/36.30  thf('37', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['36'])).
% 36.10/36.30  thf('38', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.10/36.30         (~ (r2_hidden @ X0 @ X3)
% 36.10/36.30          | (r2_hidden @ X0 @ X2)
% 36.10/36.30          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 36.10/36.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 36.10/36.30  thf('39', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X3 : $i]:
% 36.10/36.30         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 36.10/36.30      inference('simplify', [status(thm)], ['38'])).
% 36.10/36.30  thf('40', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['37', '39'])).
% 36.10/36.30  thf('41', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X3 : $i]:
% 36.10/36.30         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 36.10/36.30      inference('simplify', [status(thm)], ['38'])).
% 36.10/36.30  thf('42', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 36.10/36.30         (((X1) = (k3_xboole_0 @ X2 @ X1))
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X1 @ X1 @ X2) @ 
% 36.10/36.30             (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['40', '41'])).
% 36.10/36.30  thf('43', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['36'])).
% 36.10/36.30  thf('44', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X11 : $i]:
% 36.10/36.30         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 36.10/36.30      inference('cnf', [status(esa)], [d4_xboole_0])).
% 36.10/36.30  thf('45', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X1)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['43', '44'])).
% 36.10/36.30  thf('46', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X1)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['45'])).
% 36.10/36.30  thf('47', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['36'])).
% 36.10/36.30  thf('48', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X1))),
% 36.10/36.30      inference('clc', [status(thm)], ['46', '47'])).
% 36.10/36.30  thf('49', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         (((X2)
% 36.10/36.30            = (k3_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X2))
% 36.10/36.30          | ((X2)
% 36.10/36.30              = (k3_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 36.10/36.30                 X2)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['42', '48'])).
% 36.10/36.30  thf('50', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         ((X2)
% 36.10/36.30           = (k3_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X2))),
% 36.10/36.30      inference('simplify', [status(thm)], ['49'])).
% 36.10/36.30  thf('51', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         ((k3_xboole_0 @ X1 @ X0)
% 36.10/36.30           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('sup+', [status(thm)], ['35', '50'])).
% 36.10/36.30  thf('52', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 36.10/36.30      inference('sup+', [status(thm)], ['15', '33'])).
% 36.10/36.30  thf('53', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         ((k2_xboole_0 @ X0 @ X2)
% 36.10/36.30           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 36.10/36.30      inference('sup+', [status(thm)], ['51', '52'])).
% 36.10/36.30  thf('54', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 36.10/36.30           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 36.10/36.30      inference('sup+', [status(thm)], ['34', '53'])).
% 36.10/36.30  thf('55', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 36.10/36.30      inference('sup+', [status(thm)], ['15', '33'])).
% 36.10/36.30  thf('56', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         ((X0)
% 36.10/36.30           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 36.10/36.30      inference('demod', [status(thm)], ['54', '55'])).
% 36.10/36.30  thf('57', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         ((X2)
% 36.10/36.30           = (k2_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X2))),
% 36.10/36.30      inference('sup+', [status(thm)], ['14', '56'])).
% 36.10/36.30  thf('58', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 36.10/36.30      inference('clc', [status(thm)], ['31', '32'])).
% 36.10/36.30  thf('59', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['36'])).
% 36.10/36.30  thf('60', plain,
% 36.10/36.30      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 36.10/36.30         (~ (r2_hidden @ X4 @ X2)
% 36.10/36.30          | (r2_hidden @ X4 @ X3)
% 36.10/36.30          | (r2_hidden @ X4 @ X1)
% 36.10/36.30          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 36.10/36.30      inference('cnf', [status(esa)], [d3_xboole_0])).
% 36.10/36.30  thf('61', plain,
% 36.10/36.30      (![X1 : $i, X3 : $i, X4 : $i]:
% 36.10/36.30         ((r2_hidden @ X4 @ X1)
% 36.10/36.30          | (r2_hidden @ X4 @ X3)
% 36.10/36.30          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 36.10/36.30      inference('simplify', [status(thm)], ['60'])).
% 36.10/36.30  thf('62', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         (((k2_xboole_0 @ X1 @ X0)
% 36.10/36.30            = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 36.10/36.30          | (r2_hidden @ 
% 36.10/36.30             (sk_D_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0) @ X2) @ 
% 36.10/36.30             X1)
% 36.10/36.30          | (r2_hidden @ 
% 36.10/36.30             (sk_D_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0) @ X2) @ 
% 36.10/36.30             X0))),
% 36.10/36.30      inference('sup-', [status(thm)], ['59', '61'])).
% 36.10/36.30  thf('63', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X1))),
% 36.10/36.30      inference('clc', [status(thm)], ['46', '47'])).
% 36.10/36.30  thf('64', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ 
% 36.10/36.30           (sk_D_1 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 36.10/36.30           X1)
% 36.10/36.30          | ((k2_xboole_0 @ X0 @ X1)
% 36.10/36.30              = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))
% 36.10/36.30          | ((k2_xboole_0 @ X0 @ X1)
% 36.10/36.30              = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 36.10/36.30      inference('sup-', [status(thm)], ['62', '63'])).
% 36.10/36.30  thf('65', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['1'])).
% 36.10/36.30  thf('66', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X3 : $i]:
% 36.10/36.30         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 36.10/36.30      inference('simplify', [status(thm)], ['38'])).
% 36.10/36.30  thf('67', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 36.10/36.30          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['65', '66'])).
% 36.10/36.30  thf('68', plain,
% 36.10/36.30      (![X7 : $i, X8 : $i, X11 : $i]:
% 36.10/36.30         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 36.10/36.30      inference('cnf', [status(esa)], [d4_xboole_0])).
% 36.10/36.30  thf('69', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X1)
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X1)
% 36.10/36.30          | ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 36.10/36.30      inference('sup-', [status(thm)], ['67', '68'])).
% 36.10/36.30  thf('70', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (~ (r2_hidden @ (sk_D_1 @ X1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X1)
% 36.10/36.30          | ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 36.10/36.30      inference('simplify', [status(thm)], ['69'])).
% 36.10/36.30  thf('71', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 36.10/36.30          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 36.10/36.30      inference('eq_fact', [status(thm)], ['1'])).
% 36.10/36.30  thf('72', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('clc', [status(thm)], ['70', '71'])).
% 36.10/36.30  thf('73', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('clc', [status(thm)], ['70', '71'])).
% 36.10/36.30  thf('74', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((r2_hidden @ 
% 36.10/36.30           (sk_D_1 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 36.10/36.30           X1)
% 36.10/36.30          | ((k2_xboole_0 @ X0 @ X1) = (X0))
% 36.10/36.30          | ((k2_xboole_0 @ X0 @ X1) = (X0)))),
% 36.10/36.30      inference('demod', [status(thm)], ['64', '72', '73'])).
% 36.10/36.30  thf('75', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((k2_xboole_0 @ X0 @ X1) = (X0))
% 36.10/36.30          | (r2_hidden @ 
% 36.10/36.30             (sk_D_1 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 36.10/36.30             X1))),
% 36.10/36.30      inference('simplify', [status(thm)], ['74'])).
% 36.10/36.30  thf('76', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X3 : $i]:
% 36.10/36.30         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 36.10/36.30      inference('simplify', [status(thm)], ['38'])).
% 36.10/36.30  thf('77', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 36.10/36.30         (((k2_xboole_0 @ X1 @ X0) = (X1))
% 36.10/36.30          | (r2_hidden @ 
% 36.10/36.30             (sk_D_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 36.10/36.30             (k2_xboole_0 @ X0 @ X2)))),
% 36.10/36.30      inference('sup-', [status(thm)], ['75', '76'])).
% 36.10/36.30  thf('78', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 36.10/36.30          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X1))),
% 36.10/36.30      inference('clc', [status(thm)], ['46', '47'])).
% 36.10/36.30  thf('79', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 36.10/36.30            = (k2_xboole_0 @ X1 @ X0))
% 36.10/36.30          | ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 36.10/36.30              = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 36.10/36.30                 (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))))),
% 36.10/36.30      inference('sup-', [status(thm)], ['77', '78'])).
% 36.10/36.30  thf('80', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('clc', [status(thm)], ['70', '71'])).
% 36.10/36.30  thf('81', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         (((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 36.10/36.30            = (k2_xboole_0 @ X1 @ X0))
% 36.10/36.30          | ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 36.10/36.30              = (k2_xboole_0 @ X1 @ X0)))),
% 36.10/36.30      inference('demod', [status(thm)], ['79', '80'])).
% 36.10/36.30  thf('82', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 36.10/36.30           = (k2_xboole_0 @ X1 @ X0))),
% 36.10/36.30      inference('simplify', [status(thm)], ['81'])).
% 36.10/36.30  thf('83', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 36.10/36.30           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 36.10/36.30      inference('sup+', [status(thm)], ['58', '82'])).
% 36.10/36.30  thf('84', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))
% 36.10/36.30           = (X0))),
% 36.10/36.30      inference('sup+', [status(thm)], ['57', '83'])).
% 36.10/36.30  thf('85', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((k3_xboole_0 @ X1 @ X0)
% 36.10/36.30           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 36.10/36.30      inference('clc', [status(thm)], ['12', '13'])).
% 36.10/36.30  thf('86', plain,
% 36.10/36.30      (![X0 : $i, X1 : $i]:
% 36.10/36.30         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 36.10/36.30      inference('demod', [status(thm)], ['84', '85'])).
% 36.10/36.30  thf('87', plain, (((sk_A) != (sk_A))),
% 36.10/36.30      inference('demod', [status(thm)], ['0', '86'])).
% 36.10/36.30  thf('88', plain, ($false), inference('simplify', [status(thm)], ['87'])).
% 36.10/36.30  
% 36.10/36.30  % SZS output end Refutation
% 36.10/36.30  
% 36.13/36.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
