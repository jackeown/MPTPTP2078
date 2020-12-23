%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KVDmC8nqOJ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:38 EST 2020

% Result     : Theorem 21.54s
% Output     : Refutation 21.54s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 159 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  679 (1238 expanded)
%              Number of equality atoms :   51 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['11'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['35'])).

thf('37',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('51',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['39','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['23','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['35'])).

thf('59',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['61','66'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('69',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['17','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KVDmC8nqOJ
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:29:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 21.54/21.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.54/21.71  % Solved by: fo/fo7.sh
% 21.54/21.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.54/21.71  % done 20201 iterations in 21.252s
% 21.54/21.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.54/21.71  % SZS output start Refutation
% 21.54/21.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 21.54/21.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 21.54/21.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 21.54/21.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 21.54/21.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 21.54/21.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.54/21.71  thf(sk_A_type, type, sk_A: $i).
% 21.54/21.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 21.54/21.71  thf(sk_B_type, type, sk_B: $i).
% 21.54/21.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 21.54/21.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 21.54/21.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.54/21.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 21.54/21.71  thf(t106_xboole_1, conjecture,
% 21.54/21.71    (![A:$i,B:$i,C:$i]:
% 21.54/21.71     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 21.54/21.71       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 21.54/21.71  thf(zf_stmt_0, negated_conjecture,
% 21.54/21.71    (~( ![A:$i,B:$i,C:$i]:
% 21.54/21.71        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 21.54/21.71          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 21.54/21.71    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 21.54/21.71  thf('0', plain,
% 21.54/21.71      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 21.54/21.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.71  thf('1', plain,
% 21.54/21.71      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 21.54/21.71      inference('split', [status(esa)], ['0'])).
% 21.54/21.71  thf(d3_tarski, axiom,
% 21.54/21.71    (![A:$i,B:$i]:
% 21.54/21.71     ( ( r1_tarski @ A @ B ) <=>
% 21.54/21.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 21.54/21.71  thf('2', plain,
% 21.54/21.71      (![X1 : $i, X3 : $i]:
% 21.54/21.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 21.54/21.71      inference('cnf', [status(esa)], [d3_tarski])).
% 21.54/21.71  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 21.54/21.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.71  thf('4', plain,
% 21.54/21.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.54/21.71         (~ (r2_hidden @ X0 @ X1)
% 21.54/21.71          | (r2_hidden @ X0 @ X2)
% 21.54/21.71          | ~ (r1_tarski @ X1 @ X2))),
% 21.54/21.71      inference('cnf', [status(esa)], [d3_tarski])).
% 21.54/21.71  thf('5', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 21.54/21.71          | ~ (r2_hidden @ X0 @ sk_A))),
% 21.54/21.71      inference('sup-', [status(thm)], ['3', '4'])).
% 21.54/21.71  thf('6', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((r1_tarski @ sk_A @ X0)
% 21.54/21.71          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 21.54/21.71      inference('sup-', [status(thm)], ['2', '5'])).
% 21.54/21.71  thf(d5_xboole_0, axiom,
% 21.54/21.71    (![A:$i,B:$i,C:$i]:
% 21.54/21.71     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 21.54/21.71       ( ![D:$i]:
% 21.54/21.71         ( ( r2_hidden @ D @ C ) <=>
% 21.54/21.71           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 21.54/21.71  thf('7', plain,
% 21.54/21.71      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 21.54/21.71         (~ (r2_hidden @ X8 @ X7)
% 21.54/21.71          | (r2_hidden @ X8 @ X5)
% 21.54/21.71          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 21.54/21.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 21.54/21.71  thf('8', plain,
% 21.54/21.71      (![X5 : $i, X6 : $i, X8 : $i]:
% 21.54/21.71         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 21.54/21.71      inference('simplify', [status(thm)], ['7'])).
% 21.54/21.71  thf('9', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 21.54/21.71      inference('sup-', [status(thm)], ['6', '8'])).
% 21.54/21.71  thf('10', plain,
% 21.54/21.71      (![X1 : $i, X3 : $i]:
% 21.54/21.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 21.54/21.71      inference('cnf', [status(esa)], [d3_tarski])).
% 21.54/21.71  thf('11', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 21.54/21.71      inference('sup-', [status(thm)], ['9', '10'])).
% 21.54/21.71  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 21.54/21.71      inference('simplify', [status(thm)], ['11'])).
% 21.54/21.71  thf('13', plain,
% 21.54/21.71      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 21.54/21.71      inference('split', [status(esa)], ['0'])).
% 21.54/21.71  thf('14', plain, (((r1_tarski @ sk_A @ sk_B))),
% 21.54/21.71      inference('sup-', [status(thm)], ['12', '13'])).
% 21.54/21.71  thf('15', plain,
% 21.54/21.71      (~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 21.54/21.71      inference('split', [status(esa)], ['0'])).
% 21.54/21.71  thf('16', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 21.54/21.71      inference('sat_resolution*', [status(thm)], ['14', '15'])).
% 21.54/21.71  thf('17', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 21.54/21.71      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 21.54/21.71  thf('18', plain,
% 21.54/21.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 21.54/21.71         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 21.54/21.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 21.54/21.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 21.54/21.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 21.54/21.71  thf('19', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 21.54/21.71          | ~ (r2_hidden @ X0 @ sk_A))),
% 21.54/21.71      inference('sup-', [status(thm)], ['3', '4'])).
% 21.54/21.71  thf('20', plain,
% 21.54/21.71      (![X0 : $i, X1 : $i]:
% 21.54/21.71         ((r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ X1)
% 21.54/21.71          | ((X1) = (k4_xboole_0 @ sk_A @ X0))
% 21.54/21.71          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ 
% 21.54/21.71             (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 21.54/21.71      inference('sup-', [status(thm)], ['18', '19'])).
% 21.54/21.71  thf('21', plain,
% 21.54/21.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 21.54/21.71         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 21.54/21.71          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 21.54/21.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 21.54/21.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 21.54/21.71  thf('22', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         (((X0) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))
% 21.54/21.71          | (r2_hidden @ (sk_D @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 21.54/21.71             X0)
% 21.54/21.71          | (r2_hidden @ (sk_D @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 21.54/21.71             X0)
% 21.54/21.71          | ((X0) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))))),
% 21.54/21.71      inference('sup-', [status(thm)], ['20', '21'])).
% 21.54/21.71  thf('23', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((r2_hidden @ (sk_D @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ X0)
% 21.54/21.71          | ((X0) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))))),
% 21.54/21.71      inference('simplify', [status(thm)], ['22'])).
% 21.54/21.71  thf('24', plain,
% 21.54/21.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 21.54/21.71         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 21.54/21.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 21.54/21.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 21.54/21.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 21.54/21.71  thf('25', plain, ((r1_tarski @ sk_A @ sk_B)),
% 21.54/21.71      inference('simplify', [status(thm)], ['11'])).
% 21.54/21.71  thf('26', plain,
% 21.54/21.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.54/21.71         (~ (r2_hidden @ X0 @ X1)
% 21.54/21.71          | (r2_hidden @ X0 @ X2)
% 21.54/21.71          | ~ (r1_tarski @ X1 @ X2))),
% 21.54/21.71      inference('cnf', [status(esa)], [d3_tarski])).
% 21.54/21.71  thf('27', plain,
% 21.54/21.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 21.54/21.71      inference('sup-', [status(thm)], ['25', '26'])).
% 21.54/21.71  thf('28', plain,
% 21.54/21.71      (![X0 : $i, X1 : $i]:
% 21.54/21.71         ((r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ X1)
% 21.54/21.71          | ((X1) = (k4_xboole_0 @ sk_A @ X0))
% 21.54/21.71          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ sk_B))),
% 21.54/21.71      inference('sup-', [status(thm)], ['24', '27'])).
% 21.54/21.71  thf('29', plain,
% 21.54/21.71      (![X5 : $i, X6 : $i, X9 : $i]:
% 21.54/21.71         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 21.54/21.71          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 21.54/21.71          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 21.54/21.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 21.54/21.71  thf('30', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         (((X0) = (k4_xboole_0 @ sk_A @ sk_B))
% 21.54/21.71          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 21.54/21.71          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 21.54/21.71          | ((X0) = (k4_xboole_0 @ sk_A @ sk_B)))),
% 21.54/21.71      inference('sup-', [status(thm)], ['28', '29'])).
% 21.54/21.71  thf('31', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 21.54/21.71          | ((X0) = (k4_xboole_0 @ sk_A @ sk_B)))),
% 21.54/21.71      inference('simplify', [status(thm)], ['30'])).
% 21.54/21.71  thf(t3_boole, axiom,
% 21.54/21.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 21.54/21.71  thf('32', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 21.54/21.71      inference('cnf', [status(esa)], [t3_boole])).
% 21.54/21.71  thf('33', plain,
% 21.54/21.71      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 21.54/21.71         (~ (r2_hidden @ X8 @ X7)
% 21.54/21.71          | ~ (r2_hidden @ X8 @ X6)
% 21.54/21.71          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 21.54/21.71      inference('cnf', [status(esa)], [d5_xboole_0])).
% 21.54/21.71  thf('34', plain,
% 21.54/21.71      (![X5 : $i, X6 : $i, X8 : $i]:
% 21.54/21.71         (~ (r2_hidden @ X8 @ X6)
% 21.54/21.71          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 21.54/21.71      inference('simplify', [status(thm)], ['33'])).
% 21.54/21.71  thf('35', plain,
% 21.54/21.71      (![X0 : $i, X1 : $i]:
% 21.54/21.71         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 21.54/21.71      inference('sup-', [status(thm)], ['32', '34'])).
% 21.54/21.71  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 21.54/21.71      inference('condensation', [status(thm)], ['35'])).
% 21.54/21.71  thf('37', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 21.54/21.71      inference('sup-', [status(thm)], ['31', '36'])).
% 21.54/21.71  thf(t52_xboole_1, axiom,
% 21.54/21.71    (![A:$i,B:$i,C:$i]:
% 21.54/21.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 21.54/21.71       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 21.54/21.71  thf('38', plain,
% 21.54/21.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 21.54/21.71           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 21.54/21.71              (k3_xboole_0 @ X19 @ X21)))),
% 21.54/21.71      inference('cnf', [status(esa)], [t52_xboole_1])).
% 21.54/21.71  thf('39', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 21.54/21.71           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 21.54/21.71      inference('sup+', [status(thm)], ['37', '38'])).
% 21.54/21.71  thf('40', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 21.54/21.71      inference('cnf', [status(esa)], [t3_boole])).
% 21.54/21.71  thf(t48_xboole_1, axiom,
% 21.54/21.71    (![A:$i,B:$i]:
% 21.54/21.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 21.54/21.71  thf('41', plain,
% 21.54/21.71      (![X14 : $i, X15 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 21.54/21.71           = (k3_xboole_0 @ X14 @ X15))),
% 21.54/21.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 21.54/21.71  thf('42', plain,
% 21.54/21.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 21.54/21.71      inference('sup+', [status(thm)], ['40', '41'])).
% 21.54/21.71  thf(t2_boole, axiom,
% 21.54/21.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 21.54/21.71  thf('43', plain,
% 21.54/21.71      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 21.54/21.71      inference('cnf', [status(esa)], [t2_boole])).
% 21.54/21.71  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 21.54/21.71      inference('demod', [status(thm)], ['42', '43'])).
% 21.54/21.71  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 21.54/21.71      inference('demod', [status(thm)], ['42', '43'])).
% 21.54/21.71  thf('46', plain,
% 21.54/21.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 21.54/21.71           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 21.54/21.71              (k3_xboole_0 @ X19 @ X21)))),
% 21.54/21.71      inference('cnf', [status(esa)], [t52_xboole_1])).
% 21.54/21.71  thf('47', plain,
% 21.54/21.71      (![X0 : $i, X1 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 21.54/21.71           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 21.54/21.71      inference('sup+', [status(thm)], ['45', '46'])).
% 21.54/21.71  thf('48', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 21.54/21.71           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 21.54/21.71      inference('sup+', [status(thm)], ['44', '47'])).
% 21.54/21.71  thf('49', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 21.54/21.71      inference('cnf', [status(esa)], [t3_boole])).
% 21.54/21.71  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 21.54/21.71      inference('demod', [status(thm)], ['42', '43'])).
% 21.54/21.71  thf('51', plain,
% 21.54/21.71      (![X14 : $i, X15 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 21.54/21.71           = (k3_xboole_0 @ X14 @ X15))),
% 21.54/21.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 21.54/21.71  thf('52', plain,
% 21.54/21.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 21.54/21.71      inference('sup+', [status(thm)], ['50', '51'])).
% 21.54/21.71  thf('53', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 21.54/21.71      inference('cnf', [status(esa)], [t3_boole])).
% 21.54/21.71  thf('54', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 21.54/21.71      inference('demod', [status(thm)], ['52', '53'])).
% 21.54/21.71  thf('55', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 21.54/21.71      inference('demod', [status(thm)], ['48', '49', '54'])).
% 21.54/21.71  thf('56', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 21.54/21.71           = (k3_xboole_0 @ sk_A @ X0))),
% 21.54/21.71      inference('demod', [status(thm)], ['39', '55'])).
% 21.54/21.71  thf('57', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((r2_hidden @ (sk_D @ X0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ X0)
% 21.54/21.71          | ((X0) = (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 21.54/21.71      inference('demod', [status(thm)], ['23', '56'])).
% 21.54/21.71  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 21.54/21.71      inference('condensation', [status(thm)], ['35'])).
% 21.54/21.71  thf('59', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 21.54/21.71      inference('sup-', [status(thm)], ['57', '58'])).
% 21.54/21.71  thf(t100_xboole_1, axiom,
% 21.54/21.71    (![A:$i,B:$i]:
% 21.54/21.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 21.54/21.71  thf('60', plain,
% 21.54/21.71      (![X10 : $i, X11 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X10 @ X11)
% 21.54/21.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 21.54/21.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 21.54/21.71  thf('61', plain,
% 21.54/21.71      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 21.54/21.71      inference('sup+', [status(thm)], ['59', '60'])).
% 21.54/21.71  thf('62', plain,
% 21.54/21.71      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 21.54/21.71      inference('cnf', [status(esa)], [t2_boole])).
% 21.54/21.71  thf('63', plain,
% 21.54/21.71      (![X10 : $i, X11 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X10 @ X11)
% 21.54/21.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 21.54/21.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 21.54/21.71  thf('64', plain,
% 21.54/21.71      (![X0 : $i]:
% 21.54/21.71         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 21.54/21.71      inference('sup+', [status(thm)], ['62', '63'])).
% 21.54/21.71  thf('65', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 21.54/21.71      inference('cnf', [status(esa)], [t3_boole])).
% 21.54/21.71  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 21.54/21.71      inference('sup+', [status(thm)], ['64', '65'])).
% 21.54/21.71  thf('67', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 21.54/21.71      inference('demod', [status(thm)], ['61', '66'])).
% 21.54/21.71  thf(t79_xboole_1, axiom,
% 21.54/21.71    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 21.54/21.71  thf('68', plain,
% 21.54/21.71      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 21.54/21.71      inference('cnf', [status(esa)], [t79_xboole_1])).
% 21.54/21.71  thf('69', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 21.54/21.71      inference('sup+', [status(thm)], ['67', '68'])).
% 21.54/21.71  thf('70', plain, ($false), inference('demod', [status(thm)], ['17', '69'])).
% 21.54/21.71  
% 21.54/21.71  % SZS output end Refutation
% 21.54/21.71  
% 21.54/21.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
