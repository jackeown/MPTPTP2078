%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vwqrSb5YjG

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:58 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 188 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  696 (1592 expanded)
%              Number of equality atoms :   81 ( 200 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t141_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( r2_hidden @ A @ B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t141_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X23: $i] :
      ( ( X23
        = ( k1_tarski @ X19 ) )
      | ( ( sk_C @ X23 @ X19 )
        = X19 )
      | ( r2_hidden @ ( sk_C @ X23 @ X19 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( X22 = X19 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22 = X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X1 )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X0 )
        = X2 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X19: $i] :
      ( r2_hidden @ X19 @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('16',plain,(
    ! [X19: $i,X23: $i] :
      ( ( X23
        = ( k1_tarski @ X19 ) )
      | ( ( sk_C @ X23 @ X19 )
       != X19 )
      | ~ ( r2_hidden @ ( sk_C @ X23 @ X19 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
       != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X0 )
       != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X1 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('53',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('55',plain,(
    ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vwqrSb5YjG
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.21/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.21/1.45  % Solved by: fo/fo7.sh
% 1.21/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.45  % done 2071 iterations in 1.034s
% 1.21/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.21/1.45  % SZS output start Refutation
% 1.21/1.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.21/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.21/1.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.21/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.21/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.45  thf(t141_zfmisc_1, conjecture,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( ~( r2_hidden @ A @ B ) ) =>
% 1.21/1.45       ( ( k4_xboole_0 @
% 1.21/1.45           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.21/1.45         ( B ) ) ))).
% 1.21/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.45    (~( ![A:$i,B:$i]:
% 1.21/1.45        ( ( ~( r2_hidden @ A @ B ) ) =>
% 1.21/1.45          ( ( k4_xboole_0 @
% 1.21/1.45              ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.21/1.45            ( B ) ) ) )),
% 1.21/1.45    inference('cnf.neg', [status(esa)], [t141_zfmisc_1])).
% 1.21/1.45  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.45  thf(d1_tarski, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.21/1.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.21/1.45  thf('1', plain,
% 1.21/1.45      (![X19 : $i, X23 : $i]:
% 1.21/1.45         (((X23) = (k1_tarski @ X19))
% 1.21/1.45          | ((sk_C @ X23 @ X19) = (X19))
% 1.21/1.45          | (r2_hidden @ (sk_C @ X23 @ X19) @ X23))),
% 1.21/1.45      inference('cnf', [status(esa)], [d1_tarski])).
% 1.21/1.45  thf(d5_xboole_0, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i]:
% 1.21/1.45     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.21/1.45       ( ![D:$i]:
% 1.21/1.45         ( ( r2_hidden @ D @ C ) <=>
% 1.21/1.45           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.21/1.45  thf('2', plain,
% 1.21/1.45      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.21/1.45         (~ (r2_hidden @ X6 @ X5)
% 1.21/1.45          | (r2_hidden @ X6 @ X3)
% 1.21/1.45          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.21/1.45      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.21/1.45  thf('3', plain,
% 1.21/1.45      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.21/1.45         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.21/1.45      inference('simplify', [status(thm)], ['2'])).
% 1.21/1.45  thf('4', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (((sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) = (X2))
% 1.21/1.45          | ((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 1.21/1.45          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 1.21/1.45      inference('sup-', [status(thm)], ['1', '3'])).
% 1.21/1.45  thf('5', plain,
% 1.21/1.45      (![X19 : $i, X21 : $i, X22 : $i]:
% 1.21/1.45         (~ (r2_hidden @ X22 @ X21)
% 1.21/1.45          | ((X22) = (X19))
% 1.21/1.45          | ((X21) != (k1_tarski @ X19)))),
% 1.21/1.45      inference('cnf', [status(esa)], [d1_tarski])).
% 1.21/1.45  thf('6', plain,
% 1.21/1.45      (![X19 : $i, X22 : $i]:
% 1.21/1.45         (((X22) = (X19)) | ~ (r2_hidden @ X22 @ (k1_tarski @ X19)))),
% 1.21/1.45      inference('simplify', [status(thm)], ['5'])).
% 1.21/1.45  thf('7', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 1.21/1.45          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X1))
% 1.21/1.45          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1) = (X0)))),
% 1.21/1.45      inference('sup-', [status(thm)], ['4', '6'])).
% 1.21/1.45  thf('8', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.45         (((X0) != (X2))
% 1.21/1.45          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X0) = (X2))
% 1.21/1.45          | ((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X0)))),
% 1.21/1.45      inference('eq_fact', [status(thm)], ['7'])).
% 1.21/1.45  thf('9', plain,
% 1.21/1.45      (![X1 : $i, X2 : $i]:
% 1.21/1.45         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 1.21/1.45          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 1.21/1.45      inference('simplify', [status(thm)], ['8'])).
% 1.21/1.45  thf('10', plain,
% 1.21/1.45      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.21/1.45         (((X20) != (X19))
% 1.21/1.45          | (r2_hidden @ X20 @ X21)
% 1.21/1.45          | ((X21) != (k1_tarski @ X19)))),
% 1.21/1.45      inference('cnf', [status(esa)], [d1_tarski])).
% 1.21/1.45  thf('11', plain, (![X19 : $i]: (r2_hidden @ X19 @ (k1_tarski @ X19))),
% 1.21/1.45      inference('simplify', [status(thm)], ['10'])).
% 1.21/1.45  thf('12', plain,
% 1.21/1.45      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.21/1.45         (~ (r2_hidden @ X2 @ X3)
% 1.21/1.45          | (r2_hidden @ X2 @ X4)
% 1.21/1.45          | (r2_hidden @ X2 @ X5)
% 1.21/1.45          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.21/1.45      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.21/1.45  thf('13', plain,
% 1.21/1.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.21/1.45         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.21/1.45          | (r2_hidden @ X2 @ X4)
% 1.21/1.45          | ~ (r2_hidden @ X2 @ X3))),
% 1.21/1.45      inference('simplify', [status(thm)], ['12'])).
% 1.21/1.45  thf('14', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((r2_hidden @ X0 @ X1)
% 1.21/1.45          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.21/1.45      inference('sup-', [status(thm)], ['11', '13'])).
% 1.21/1.45  thf('15', plain,
% 1.21/1.45      (![X1 : $i, X2 : $i]:
% 1.21/1.45         (((k4_xboole_0 @ (k1_tarski @ X2) @ X1) = (k1_tarski @ X2))
% 1.21/1.45          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X2) @ X1) @ X2) = (X2)))),
% 1.21/1.45      inference('simplify', [status(thm)], ['8'])).
% 1.21/1.45  thf('16', plain,
% 1.21/1.45      (![X19 : $i, X23 : $i]:
% 1.21/1.45         (((X23) = (k1_tarski @ X19))
% 1.21/1.45          | ((sk_C @ X23 @ X19) != (X19))
% 1.21/1.45          | ~ (r2_hidden @ (sk_C @ X23 @ X19) @ X23))),
% 1.21/1.45      inference('cnf', [status(esa)], [d1_tarski])).
% 1.21/1.45  thf('17', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.21/1.45          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.21/1.45          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 1.21/1.45          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.21/1.45      inference('sup-', [status(thm)], ['15', '16'])).
% 1.21/1.45  thf('18', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (((sk_C @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X0) != (X0))
% 1.21/1.45          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.21/1.45          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.21/1.45      inference('simplify', [status(thm)], ['17'])).
% 1.21/1.45  thf('19', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((r2_hidden @ X1 @ X0)
% 1.21/1.45          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 1.21/1.45          | ((sk_C @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0) @ X1) != (X1)))),
% 1.21/1.45      inference('sup-', [status(thm)], ['14', '18'])).
% 1.21/1.45  thf('20', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (((X0) != (X0))
% 1.21/1.45          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.21/1.45          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.21/1.45          | (r2_hidden @ X0 @ X1))),
% 1.21/1.45      inference('sup-', [status(thm)], ['9', '19'])).
% 1.21/1.45  thf('21', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((r2_hidden @ X0 @ X1)
% 1.21/1.45          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.21/1.45      inference('simplify', [status(thm)], ['20'])).
% 1.21/1.45  thf(t95_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( k3_xboole_0 @ A @ B ) =
% 1.21/1.45       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.21/1.45  thf('22', plain,
% 1.21/1.45      (![X17 : $i, X18 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X17 @ X18)
% 1.21/1.45           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 1.21/1.45              (k2_xboole_0 @ X17 @ X18)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.21/1.45  thf(t91_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i,C:$i]:
% 1.21/1.45     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.21/1.45       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.21/1.45  thf('23', plain,
% 1.21/1.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.21/1.45           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('24', plain,
% 1.21/1.45      (![X17 : $i, X18 : $i]:
% 1.21/1.45         ((k3_xboole_0 @ X17 @ X18)
% 1.21/1.45           = (k5_xboole_0 @ X17 @ 
% 1.21/1.45              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 1.21/1.45      inference('demod', [status(thm)], ['22', '23'])).
% 1.21/1.45  thf(t92_xboole_1, axiom,
% 1.21/1.45    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.21/1.45  thf('25', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 1.21/1.45      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.21/1.45  thf('26', plain,
% 1.21/1.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.21/1.45           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('27', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['25', '26'])).
% 1.21/1.45  thf('28', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 1.21/1.45      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.21/1.45  thf('29', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['25', '26'])).
% 1.21/1.45  thf('30', plain,
% 1.21/1.45      (![X0 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['28', '29'])).
% 1.21/1.45  thf(t5_boole, axiom,
% 1.21/1.45    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.21/1.45  thf('31', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.21/1.45      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.45  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['30', '31'])).
% 1.21/1.45  thf('33', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('demod', [status(thm)], ['27', '32'])).
% 1.21/1.45  thf('34', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('sup+', [status(thm)], ['24', '33'])).
% 1.21/1.45  thf(t100_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.21/1.45  thf('35', plain,
% 1.21/1.45      (![X8 : $i, X9 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ X8 @ X9)
% 1.21/1.45           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.21/1.45  thf('36', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['34', '35'])).
% 1.21/1.45  thf('37', plain,
% 1.21/1.45      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 1.21/1.45           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 1.21/1.45      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.21/1.45  thf('38', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 1.21/1.45      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.21/1.45  thf('39', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 1.21/1.45           = (k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['37', '38'])).
% 1.21/1.45  thf('40', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('demod', [status(thm)], ['27', '32'])).
% 1.21/1.45  thf('41', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['39', '40'])).
% 1.21/1.45  thf('42', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.21/1.45      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.45  thf('43', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.21/1.45      inference('demod', [status(thm)], ['41', '42'])).
% 1.21/1.45  thf('44', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['36', '43'])).
% 1.21/1.45  thf('45', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (((k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 1.21/1.45            (k1_tarski @ X0)) = (X1))
% 1.21/1.45          | (r2_hidden @ X0 @ X1))),
% 1.21/1.45      inference('sup+', [status(thm)], ['21', '44'])).
% 1.21/1.45  thf('46', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.21/1.45      inference('demod', [status(thm)], ['41', '42'])).
% 1.21/1.45  thf('47', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.21/1.45      inference('demod', [status(thm)], ['27', '32'])).
% 1.21/1.45  thf('48', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('sup+', [status(thm)], ['46', '47'])).
% 1.21/1.45  thf(commutativity_k2_xboole_0, axiom,
% 1.21/1.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.21/1.45  thf('49', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.21/1.45  thf('50', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.45      inference('demod', [status(thm)], ['34', '35'])).
% 1.21/1.45  thf('51', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.21/1.45           = (k4_xboole_0 @ X0 @ X1))),
% 1.21/1.45      inference('sup+', [status(thm)], ['49', '50'])).
% 1.21/1.45  thf('52', plain,
% 1.21/1.45      (![X0 : $i, X1 : $i]:
% 1.21/1.45         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 1.21/1.45          | (r2_hidden @ X0 @ X1))),
% 1.21/1.45      inference('demod', [status(thm)], ['45', '48', '51'])).
% 1.21/1.45  thf('53', plain,
% 1.21/1.45      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 1.21/1.45         (k1_tarski @ sk_A)) != (sk_B))),
% 1.21/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.45  thf(t40_xboole_1, axiom,
% 1.21/1.45    (![A:$i,B:$i]:
% 1.21/1.45     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.21/1.45  thf('54', plain,
% 1.21/1.45      (![X10 : $i, X11 : $i]:
% 1.21/1.45         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 1.21/1.45           = (k4_xboole_0 @ X10 @ X11))),
% 1.21/1.45      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.21/1.45  thf('55', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 1.21/1.45      inference('demod', [status(thm)], ['53', '54'])).
% 1.21/1.45  thf('56', plain, ((((sk_B) != (sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 1.21/1.45      inference('sup-', [status(thm)], ['52', '55'])).
% 1.21/1.45  thf('57', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.21/1.45      inference('simplify', [status(thm)], ['56'])).
% 1.21/1.45  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 1.21/1.45  
% 1.21/1.45  % SZS output end Refutation
% 1.21/1.45  
% 1.21/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
