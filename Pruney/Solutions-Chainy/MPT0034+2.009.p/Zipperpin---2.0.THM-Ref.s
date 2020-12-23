%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4gLRHkDl4S

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:55 EST 2020

% Result     : Theorem 3.89s
% Output     : Refutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 387 expanded)
%              Number of leaves         :   12 ( 105 expanded)
%              Depth                    :   17
%              Number of atoms          : 1270 (5226 expanded)
%              Number of equality atoms :   57 ( 274 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t27_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ) ),
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
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_A @ X0 ) @ X1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      | ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X3 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X1 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ( ( k3_xboole_0 @ X0 @ X2 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['24','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('63',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D_1 )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_D_1 )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ sk_C_1 @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ X1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_C_1 @ X0 )
        = ( k3_xboole_0 @ sk_D_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ sk_C_1 @ X0 )
        = ( k3_xboole_0 @ sk_D_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ X0 )
      = ( k3_xboole_0 @ sk_D_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ X0 )
      = ( k3_xboole_0 @ sk_D_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ sk_C_1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ sk_C_1 ) @ X0 ) @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['60','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ sk_C_1 ) @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ sk_C_1 ) @ X0 ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('84',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('87',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('88',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ sk_C_1 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['82','94'])).

thf('96',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['40','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4gLRHkDl4S
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:29:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.89/4.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.89/4.08  % Solved by: fo/fo7.sh
% 3.89/4.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.89/4.08  % done 3277 iterations in 3.626s
% 3.89/4.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.89/4.08  % SZS output start Refutation
% 3.89/4.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.89/4.08  thf(sk_D_1_type, type, sk_D_1: $i).
% 3.89/4.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.89/4.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.89/4.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.89/4.08  thf(sk_B_type, type, sk_B: $i).
% 3.89/4.08  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.89/4.08  thf(sk_A_type, type, sk_A: $i).
% 3.89/4.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.89/4.08  thf(t27_xboole_1, conjecture,
% 3.89/4.08    (![A:$i,B:$i,C:$i,D:$i]:
% 3.89/4.08     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 3.89/4.08       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ))).
% 3.89/4.08  thf(zf_stmt_0, negated_conjecture,
% 3.89/4.08    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.89/4.08        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 3.89/4.08          ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ D ) ) ) )),
% 3.89/4.08    inference('cnf.neg', [status(esa)], [t27_xboole_1])).
% 3.89/4.08  thf('0', plain,
% 3.89/4.08      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 3.89/4.08          (k3_xboole_0 @ sk_B @ sk_D_1))),
% 3.89/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.08  thf(d4_xboole_0, axiom,
% 3.89/4.08    (![A:$i,B:$i,C:$i]:
% 3.89/4.08     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.89/4.08       ( ![D:$i]:
% 3.89/4.08         ( ( r2_hidden @ D @ C ) <=>
% 3.89/4.08           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.89/4.08  thf('1', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.89/4.08         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 3.89/4.08          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 3.89/4.08          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.89/4.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.89/4.08  thf('2', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('eq_fact', [status(thm)], ['1'])).
% 3.89/4.08  thf(d3_tarski, axiom,
% 3.89/4.08    (![A:$i,B:$i]:
% 3.89/4.08     ( ( r1_tarski @ A @ B ) <=>
% 3.89/4.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.89/4.08  thf('3', plain,
% 3.89/4.08      (![X1 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('4', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.89/4.08         (~ (r2_hidden @ X8 @ X7)
% 3.89/4.08          | (r2_hidden @ X8 @ X5)
% 3.89/4.08          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 3.89/4.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.89/4.08  thf('5', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.89/4.08         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['4'])).
% 3.89/4.08  thf('6', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.89/4.08          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 3.89/4.08      inference('sup-', [status(thm)], ['3', '5'])).
% 3.89/4.08  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 3.89/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.08  thf('8', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (~ (r2_hidden @ X0 @ X1)
% 3.89/4.08          | (r2_hidden @ X0 @ X2)
% 3.89/4.08          | ~ (r1_tarski @ X1 @ X2))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('9', plain,
% 3.89/4.08      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 3.89/4.08      inference('sup-', [status(thm)], ['7', '8'])).
% 3.89/4.08  thf('10', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X1)
% 3.89/4.08          | (r2_hidden @ (sk_C @ X1 @ (k3_xboole_0 @ sk_A @ X0)) @ sk_B))),
% 3.89/4.08      inference('sup-', [status(thm)], ['6', '9'])).
% 3.89/4.08  thf('11', plain,
% 3.89/4.08      (![X1 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('12', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 3.89/4.08          | (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.89/4.08      inference('sup-', [status(thm)], ['10', '11'])).
% 3.89/4.08  thf('13', plain,
% 3.89/4.08      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 3.89/4.08      inference('simplify', [status(thm)], ['12'])).
% 3.89/4.08  thf('14', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (~ (r2_hidden @ X0 @ X1)
% 3.89/4.08          | (r2_hidden @ X0 @ X2)
% 3.89/4.08          | ~ (r1_tarski @ X1 @ X2))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('15', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ X1 @ sk_B)
% 3.89/4.08          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 3.89/4.08      inference('sup-', [status(thm)], ['13', '14'])).
% 3.89/4.08  thf('16', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (((k3_xboole_0 @ sk_A @ X0)
% 3.89/4.08            = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_A @ X0)))
% 3.89/4.08          | (r2_hidden @ 
% 3.89/4.08             (sk_D @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_A @ X0) @ X1) @ 
% 3.89/4.08             sk_B))),
% 3.89/4.08      inference('sup-', [status(thm)], ['2', '15'])).
% 3.89/4.08  thf('17', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('eq_fact', [status(thm)], ['1'])).
% 3.89/4.08  thf('18', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.89/4.08         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.89/4.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.89/4.08  thf('19', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('sup-', [status(thm)], ['17', '18'])).
% 3.89/4.08  thf('20', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['19'])).
% 3.89/4.08  thf('21', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('eq_fact', [status(thm)], ['1'])).
% 3.89/4.08  thf('22', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 3.89/4.08      inference('clc', [status(thm)], ['20', '21'])).
% 3.89/4.08  thf('23', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         (((k3_xboole_0 @ sk_A @ X0)
% 3.89/4.08            = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))
% 3.89/4.08          | ((k3_xboole_0 @ sk_A @ X0)
% 3.89/4.08              = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))))),
% 3.89/4.08      inference('sup-', [status(thm)], ['16', '22'])).
% 3.89/4.08  thf('24', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_A @ X0)
% 3.89/4.08           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['23'])).
% 3.89/4.08  thf('25', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.89/4.08         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 3.89/4.08          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 3.89/4.08          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.89/4.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.89/4.08  thf('26', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.89/4.08      inference('eq_fact', [status(thm)], ['25'])).
% 3.89/4.08  thf('27', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.89/4.08         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 3.89/4.08          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 3.89/4.08          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.89/4.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.89/4.08  thf('28', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.89/4.08         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['4'])).
% 3.89/4.08  thf('29', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X3)
% 3.89/4.08          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X2 @ X3))
% 3.89/4.08          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X1))),
% 3.89/4.08      inference('sup-', [status(thm)], ['27', '28'])).
% 3.89/4.08  thf('30', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X0)
% 3.89/4.08          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('eq_fact', [status(thm)], ['29'])).
% 3.89/4.08  thf('31', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X9 : $i]:
% 3.89/4.08         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 3.89/4.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.89/4.08  thf('32', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ 
% 3.89/4.08               (k3_xboole_0 @ X0 @ X2))
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X1)
% 3.89/4.08          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('sup-', [status(thm)], ['30', '31'])).
% 3.89/4.08  thf('33', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ X1)
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X0 @ X2) @ X0 @ X1) @ 
% 3.89/4.08               (k3_xboole_0 @ X0 @ X2))
% 3.89/4.08          | ((k3_xboole_0 @ X0 @ X2) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['32'])).
% 3.89/4.08  thf('34', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (((k3_xboole_0 @ X1 @ X0)
% 3.89/4.08            = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 3.89/4.08          | ((k3_xboole_0 @ X1 @ X0)
% 3.89/4.08              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 3.89/4.08          | ~ (r2_hidden @ 
% 3.89/4.08               (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.89/4.08               (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('sup-', [status(thm)], ['26', '33'])).
% 3.89/4.08  thf('35', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (~ (r2_hidden @ 
% 3.89/4.08             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.89/4.08             (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08          | ((k3_xboole_0 @ X1 @ X0)
% 3.89/4.08              = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['34'])).
% 3.89/4.08  thf('36', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.89/4.08      inference('eq_fact', [status(thm)], ['25'])).
% 3.89/4.08  thf('37', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ X1 @ X0)
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 3.89/4.08      inference('clc', [status(thm)], ['35', '36'])).
% 3.89/4.08  thf('38', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.89/4.08      inference('sup+', [status(thm)], ['24', '37'])).
% 3.89/4.08  thf('39', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_A @ X0)
% 3.89/4.08           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['23'])).
% 3.89/4.08  thf('40', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_A @ X0)
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.89/4.08      inference('demod', [status(thm)], ['38', '39'])).
% 3.89/4.08  thf('41', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ X1 @ X0)
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 3.89/4.08      inference('clc', [status(thm)], ['35', '36'])).
% 3.89/4.08  thf('42', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('eq_fact', [status(thm)], ['1'])).
% 3.89/4.08  thf('43', plain,
% 3.89/4.08      (![X1 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('44', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 3.89/4.08         (~ (r2_hidden @ X8 @ X7)
% 3.89/4.08          | (r2_hidden @ X8 @ X6)
% 3.89/4.08          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 3.89/4.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.89/4.08  thf('45', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.89/4.08         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['44'])).
% 3.89/4.08  thf('46', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.89/4.08          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 3.89/4.08      inference('sup-', [status(thm)], ['43', '45'])).
% 3.89/4.08  thf('47', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.89/4.08         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['44'])).
% 3.89/4.08  thf('48', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 3.89/4.08          | (r2_hidden @ 
% 3.89/4.08             (sk_C @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0))),
% 3.89/4.08      inference('sup-', [status(thm)], ['46', '47'])).
% 3.89/4.08  thf('49', plain,
% 3.89/4.08      (![X1 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('50', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 3.89/4.08          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 3.89/4.08      inference('sup-', [status(thm)], ['48', '49'])).
% 3.89/4.08  thf('51', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 3.89/4.08      inference('simplify', [status(thm)], ['50'])).
% 3.89/4.08  thf('52', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (~ (r2_hidden @ X0 @ X1)
% 3.89/4.08          | (r2_hidden @ X0 @ X2)
% 3.89/4.08          | ~ (r1_tarski @ X1 @ X2))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('53', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.89/4.08         ((r2_hidden @ X3 @ X0)
% 3.89/4.08          | ~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.89/4.08      inference('sup-', [status(thm)], ['51', '52'])).
% 3.89/4.08  thf('54', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.89/4.08         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08            = (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))
% 3.89/4.08          | (r2_hidden @ 
% 3.89/4.08             (sk_D @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.89/4.08              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3) @ 
% 3.89/4.08             X0))),
% 3.89/4.08      inference('sup-', [status(thm)], ['42', '53'])).
% 3.89/4.08  thf('55', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 3.89/4.08      inference('clc', [status(thm)], ['20', '21'])).
% 3.89/4.08  thf('56', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))
% 3.89/4.08          | ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08              = (k3_xboole_0 @ X0 @ 
% 3.89/4.08                 (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 3.89/4.08      inference('sup-', [status(thm)], ['54', '55'])).
% 3.89/4.08  thf('57', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.89/4.08      inference('simplify', [status(thm)], ['56'])).
% 3.89/4.08  thf('58', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 3.89/4.08           (k3_xboole_0 @ X2 @ X1))
% 3.89/4.08           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 3.89/4.08      inference('sup+', [status(thm)], ['41', '57'])).
% 3.89/4.08  thf('59', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ X1 @ X0)
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 3.89/4.08      inference('clc', [status(thm)], ['35', '36'])).
% 3.89/4.08  thf('60', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 3.89/4.08           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 3.89/4.08      inference('demod', [status(thm)], ['58', '59'])).
% 3.89/4.08  thf('61', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 3.89/4.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('eq_fact', [status(thm)], ['1'])).
% 3.89/4.08  thf('62', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.89/4.08          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 3.89/4.08      inference('sup-', [status(thm)], ['3', '5'])).
% 3.89/4.08  thf('63', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 3.89/4.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.08  thf('64', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (~ (r2_hidden @ X0 @ X1)
% 3.89/4.08          | (r2_hidden @ X0 @ X2)
% 3.89/4.08          | ~ (r1_tarski @ X1 @ X2))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('65', plain,
% 3.89/4.08      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 3.89/4.08      inference('sup-', [status(thm)], ['63', '64'])).
% 3.89/4.08  thf('66', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ sk_C_1 @ X0) @ X1)
% 3.89/4.08          | (r2_hidden @ (sk_C @ X1 @ (k3_xboole_0 @ sk_C_1 @ X0)) @ sk_D_1))),
% 3.89/4.08      inference('sup-', [status(thm)], ['62', '65'])).
% 3.89/4.08  thf('67', plain,
% 3.89/4.08      (![X1 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('68', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D_1)
% 3.89/4.08          | (r1_tarski @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D_1))),
% 3.89/4.08      inference('sup-', [status(thm)], ['66', '67'])).
% 3.89/4.08  thf('69', plain,
% 3.89/4.08      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D_1)),
% 3.89/4.08      inference('simplify', [status(thm)], ['68'])).
% 3.89/4.08  thf('70', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (~ (r2_hidden @ X0 @ X1)
% 3.89/4.08          | (r2_hidden @ X0 @ X2)
% 3.89/4.08          | ~ (r1_tarski @ X1 @ X2))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('71', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((r2_hidden @ X1 @ sk_D_1)
% 3.89/4.08          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 3.89/4.08      inference('sup-', [status(thm)], ['69', '70'])).
% 3.89/4.08  thf('72', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (((k3_xboole_0 @ sk_C_1 @ X0)
% 3.89/4.08            = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_C_1 @ X0)))
% 3.89/4.08          | (r2_hidden @ 
% 3.89/4.08             (sk_D @ (k3_xboole_0 @ sk_C_1 @ X0) @ 
% 3.89/4.08              (k3_xboole_0 @ sk_C_1 @ X0) @ X1) @ 
% 3.89/4.08             sk_D_1))),
% 3.89/4.08      inference('sup-', [status(thm)], ['61', '71'])).
% 3.89/4.08  thf('73', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 3.89/4.08      inference('clc', [status(thm)], ['20', '21'])).
% 3.89/4.08  thf('74', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         (((k3_xboole_0 @ sk_C_1 @ X0)
% 3.89/4.08            = (k3_xboole_0 @ sk_D_1 @ (k3_xboole_0 @ sk_C_1 @ X0)))
% 3.89/4.08          | ((k3_xboole_0 @ sk_C_1 @ X0)
% 3.89/4.08              = (k3_xboole_0 @ sk_D_1 @ (k3_xboole_0 @ sk_C_1 @ X0))))),
% 3.89/4.08      inference('sup-', [status(thm)], ['72', '73'])).
% 3.89/4.08  thf('75', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_C_1 @ X0)
% 3.89/4.08           = (k3_xboole_0 @ sk_D_1 @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['74'])).
% 3.89/4.08  thf('76', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ X1 @ X0)
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 3.89/4.08      inference('clc', [status(thm)], ['35', '36'])).
% 3.89/4.08  thf('77', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_D_1 @ (k3_xboole_0 @ sk_C_1 @ X0))
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D_1))),
% 3.89/4.08      inference('sup+', [status(thm)], ['75', '76'])).
% 3.89/4.08  thf('78', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_C_1 @ X0)
% 3.89/4.08           = (k3_xboole_0 @ sk_D_1 @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['74'])).
% 3.89/4.08  thf('79', plain,
% 3.89/4.08      (![X0 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_C_1 @ X0)
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D_1))),
% 3.89/4.08      inference('demod', [status(thm)], ['77', '78'])).
% 3.89/4.08  thf('80', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ sk_C_1 @ 
% 3.89/4.08           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ sk_C_1) @ X0))
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ sk_C_1) @ X0) @ 
% 3.89/4.08              sk_D_1))),
% 3.89/4.08      inference('sup+', [status(thm)], ['60', '79'])).
% 3.89/4.08  thf('81', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 3.89/4.08           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 3.89/4.08      inference('demod', [status(thm)], ['58', '59'])).
% 3.89/4.08  thf('82', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ sk_C_1) @ X0)
% 3.89/4.08           = (k3_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ sk_C_1) @ X0) @ 
% 3.89/4.08              sk_D_1))),
% 3.89/4.08      inference('demod', [status(thm)], ['80', '81'])).
% 3.89/4.08  thf('83', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.89/4.08          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 3.89/4.08      inference('sup-', [status(thm)], ['3', '5'])).
% 3.89/4.08  thf('84', plain,
% 3.89/4.08      (![X5 : $i, X6 : $i, X8 : $i]:
% 3.89/4.08         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 3.89/4.08      inference('simplify', [status(thm)], ['44'])).
% 3.89/4.08  thf('85', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 3.89/4.08          | (r2_hidden @ 
% 3.89/4.08             (sk_C @ X3 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ X0))),
% 3.89/4.08      inference('sup-', [status(thm)], ['83', '84'])).
% 3.89/4.08  thf('86', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.89/4.08          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 3.89/4.08      inference('sup-', [status(thm)], ['43', '45'])).
% 3.89/4.08  thf('87', plain,
% 3.89/4.08      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.89/4.08         (~ (r2_hidden @ X4 @ X5)
% 3.89/4.08          | ~ (r2_hidden @ X4 @ X6)
% 3.89/4.08          | (r2_hidden @ X4 @ X7)
% 3.89/4.08          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 3.89/4.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.89/4.08  thf('88', plain,
% 3.89/4.08      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.89/4.08         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 3.89/4.08          | ~ (r2_hidden @ X4 @ X6)
% 3.89/4.08          | ~ (r2_hidden @ X4 @ X5))),
% 3.89/4.08      inference('simplify', [status(thm)], ['87'])).
% 3.89/4.08  thf('89', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.89/4.08          | ~ (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 3.89/4.08          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.89/4.08             (k3_xboole_0 @ X3 @ X0)))),
% 3.89/4.08      inference('sup-', [status(thm)], ['86', '88'])).
% 3.89/4.08  thf('90', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X3)
% 3.89/4.08          | (r2_hidden @ 
% 3.89/4.08             (sk_C @ X3 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1)) @ 
% 3.89/4.08             (k3_xboole_0 @ X0 @ X1))
% 3.89/4.08          | (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X3))),
% 3.89/4.08      inference('sup-', [status(thm)], ['85', '89'])).
% 3.89/4.08  thf('91', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.89/4.08         ((r2_hidden @ 
% 3.89/4.08           (sk_C @ X3 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1)) @ 
% 3.89/4.08           (k3_xboole_0 @ X0 @ X1))
% 3.89/4.08          | (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X3))),
% 3.89/4.08      inference('simplify', [status(thm)], ['90'])).
% 3.89/4.08  thf('92', plain,
% 3.89/4.08      (![X1 : $i, X3 : $i]:
% 3.89/4.08         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.89/4.08      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.08  thf('93', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 3.89/4.08           (k3_xboole_0 @ X1 @ X0))
% 3.89/4.08          | (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 3.89/4.08             (k3_xboole_0 @ X1 @ X0)))),
% 3.89/4.08      inference('sup-', [status(thm)], ['91', '92'])).
% 3.89/4.08  thf('94', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.08         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 3.89/4.08          (k3_xboole_0 @ X1 @ X0))),
% 3.89/4.08      inference('simplify', [status(thm)], ['93'])).
% 3.89/4.08  thf('95', plain,
% 3.89/4.08      (![X0 : $i, X1 : $i]:
% 3.89/4.08         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ sk_C_1) @ X0) @ 
% 3.89/4.08          (k3_xboole_0 @ X0 @ sk_D_1))),
% 3.89/4.08      inference('sup+', [status(thm)], ['82', '94'])).
% 3.89/4.08  thf('96', plain,
% 3.89/4.08      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 3.89/4.08        (k3_xboole_0 @ sk_B @ sk_D_1))),
% 3.89/4.08      inference('sup+', [status(thm)], ['40', '95'])).
% 3.89/4.08  thf('97', plain, ($false), inference('demod', [status(thm)], ['0', '96'])).
% 3.89/4.08  
% 3.89/4.08  % SZS output end Refutation
% 3.89/4.08  
% 3.89/4.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
